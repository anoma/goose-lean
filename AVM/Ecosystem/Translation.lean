import AVM.Ecosystem
import Prelude
import AVM.Class.Translation
import AVM.Ecosystem.AppData
import AVM.Logic
import AVM.Action

namespace AVM.Ecosystem

open AVM.Action

def Function.parseObjectArgs
  {lab : Ecosystem.Label}
  (consumed : List Anoma.Resource)
  (funId : lab.FunctionId)
  : Option funId.Selves
  :=
  let try consumedVec : Vector Anoma.Resource funId.numObjectArgs := consumed.toSizedVector
  let mkConsumedObject (a : funId.ObjectArgNames) : Option (Object a.classId.label) := Object.fromResource (consumedVec.get a.ix)
  @FinEnum.decImageOption'
        funId.ObjectArgNames
        (lab.objectArgNamesEnum funId)
        (fun a => Object a.classId.label)
        mkConsumedObject

def Function.logic
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Logic.Args lab)
  (funId : lab.FunctionId)
  (fargs : funId.Args.type)
  : Bool :=
  let fn : Function funId := eco.functions funId
  let try (argsConsumedSelves, argsDestroyed) :=
      args.consumed |> Logic.filterOutDummy |>.splitAtExact funId.numObjectArgs
  let try argsConsumedObjects : funId.Selves := Function.parseObjectArgs argsConsumedSelves.toList funId
  let consumedSelvesList : List SomeObject :=
     (lab.objectArgNamesEnum funId).toList.map
     (fun arg => argsConsumedObjects arg |>.toSomeObject)
  (eco.functions funId).invariant argsConsumedObjects fargs
   && Logic.checkResourcesData consumedSelvesList argsConsumedSelves.toList
   && let funRes : FunctionResult := fn.body argsConsumedObjects fargs
      let createdObjects : List SomeObject := funRes.created
      let destroyedObjects : List SomeObject := funRes.destroyed.map SomeConsumableObject.toSomeObject
      let try (argsCreated, argsDestroyedEph) := args.created |> Logic.filterOutDummy
              |>.splitAtExact createdObjects.length
      Logic.checkResourcesData createdObjects argsCreated.toList
      && Logic.checkResourcesData destroyedObjects argsDestroyed
      && Logic.checkResourcesData destroyedObjects argsDestroyedEph
      && Logic.checkResourcesPersistent args.consumed
      && Logic.checkResourcesPersistent argsCreated.toList
      && Logic.checkResourcesEphemeral argsDestroyedEph

def Function.action
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Logic.Args lab)
  (funId : lab.FunctionId)
  (fargs : funId.Args.type)
  (keys : funId.ObjectArgNames → Anoma.NullifierKey)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) := do
  let fn : Function funId := eco.functions funId
  let try consumedObjects : funId.Selves := Function.parseObjectArgs args.consumed funId
  let try consumedSelves : List SomeConsumedObject :=
    (lab.objectArgNamesEnum funId).toList
    |>.map (fun arg =>
      (consumedObjects arg).toSomeObject
      |> SomeObject.toConsumable false (keys arg)
      |> SomeConsumableObject.consume)
    |>.getSome
  let funRes : FunctionResult := fn.body consumedObjects fargs
  let createdObjects : List CreatedObject := funRes.created |>
      List.map (fun x => CreatedObject.fromSomeObject x (ephemeral := false))
  let try destroyed : List SomeConsumedObject := funRes.destroyed.map (·.consume) |>.getSome
  let destroyedEph : List CreatedObject := destroyed.map CreatedObject.balanceDestroyed
  let r ← Action.create lab (.functionId funId) fargs (consumedSelves ++ destroyed) (createdObjects ++ destroyedEph)
  pure (some r)

private def logic'
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Logic.Args lab)
  : Bool :=
  -- Check if the logic is consumed. We should not rely on app data (args.data)
  -- to detect the consumed case, because then someone could simply turn
  -- off the checks by providing malicious app data
  match args.status with
  | Created => true
  | Consumed =>
    match args.data with
    | {memberId := .falseLogicId, ..} => false
    | {memberId := .classMember mem, memberArgs} => Class.checkClassMemberLogic args eco mem memberArgs
    | {memberId := .functionId fn, memberArgs} => Function.logic eco args fn memberArgs

def logic
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Anoma.Logic.Args SomeAppData) : Bool :=
  let try appData := tryCast args.data.appData
  logic' eco { args with data := appData }
