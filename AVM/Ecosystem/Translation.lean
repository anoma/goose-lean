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
  (funData : FunctionData)
  (fargs : funId.Args.type)
  : Bool :=
  let fn : Function funId := eco.functions funId
  let try (argsConsumedSelves, argsConstructedEph, argsDestroyed, PUnit.unit) :=
      args.consumed
      |> Logic.filterOutDummy
      |>.splitsExact [funId.numObjectArgs, funData.numConstructed, funData.numDestroyed]
  let try argsConsumedObjects : funId.Selves := Function.parseObjectArgs argsConsumedSelves.toList funId
  (eco.functions funId).invariant argsConsumedObjects fargs
   && let funRes : FunctionResult funId := fn.body argsConsumedObjects fargs
      let createdObjects : List SomeObject := funRes.assembled
      let destroyedObjects : List SomeObject := funRes.destroyed.map SomeConsumableObject.toSomeObject
      let constructedObjects : List SomeObject := funRes.constructed
      let consumedDestroyedObjects : List SomeObject :=
        funId.objectArgNames.filterMap (fun arg => match funRes.argDeconstruction arg with
        | .Destroyed => argsConsumedObjects arg |>.toSomeObject |> some
        | .Disassembled => none)
      let try (argsCreated, argsConstructed, argsDestroyedEph, argsSelvesDestroyedEph, PUnit.unit) :=
        args.created
        |> Logic.filterOutDummy
        |>.splitsExact [createdObjects.length, funData.numConstructed, funData.numDestroyed, funData.numSelvesDestroyed]
      let createdObjectsData : List SomeObjectData :=
        createdObjects.map SomeObject.toSomeObjectData
      let constructedObjectsData : List SomeObjectData :=
        constructedObjects.map SomeObject.toSomeObjectData
      let destroyedObjectsData : List SomeObjectData :=
        destroyedObjects.map SomeObject.toSomeObjectData
      let consumedDestroyedObjectsData : List SomeObjectData :=
        consumedDestroyedObjects.map SomeObject.toSomeObjectData
      Logic.checkResourcesData createdObjectsData argsCreated.toList
        && Logic.checkResourcesData destroyedObjectsData argsDestroyed.toList
        && Logic.checkResourcesData destroyedObjectsData argsDestroyedEph.toList
        && Logic.checkResourcesData constructedObjectsData argsConstructed.toList
        && Logic.checkResourcesData constructedObjectsData argsConstructedEph.toList
        && Logic.checkResourcesData consumedDestroyedObjectsData argsSelvesDestroyedEph.toList
        && Logic.checkResourcesPersistent argsConsumedSelves.toList
        && Logic.checkResourcesPersistent argsDestroyed.toList
        && Logic.checkResourcesPersistent argsCreated.toList
        && Logic.checkResourcesEphemeral argsConstructedEph.toList
        && Logic.checkResourcesEphemeral argsDestroyedEph.toList
        && Logic.checkResourcesEphemeral argsSelvesDestroyedEph.toList
        && Logic.checkResourcesEphemeral argsConstructedEph.toList

def Function.action
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Logic.Args lab)
  (funId : lab.FunctionId)
  (fargs : funId.Args.type)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) := do
  let fn : Function funId := eco.functions funId
  let try consumedObjects : funId.Selves := Function.parseObjectArgs args.consumed funId
  let try consumedSelves : List (funId.ObjectArgNames × SomeConsumedObject) :=
    (lab.objectArgNamesEnum funId).toList
    |>.map (fun (arg : funId.ObjectArgNames) => do
      let try obj := consumedObjects arg
                     |>.toSomeObject
                     |> SomeObject.toConsumable false
                     |> SomeConsumableObject.consume
      some (arg, obj))
    |>.getSome
  let funRes : FunctionResult funId := fn.body consumedObjects fargs
  let selvesDestroyedEph : List CreatedObject :=
    consumedSelves.filterMap (fun (arg, consumed) =>
      match funRes.argDeconstruction arg with
      | .Destroyed => some (consumed.balanceDestroyed)
      | .Disassembled => none)
  let createdObjects : List CreatedObject := funRes.assembled |>
      List.map (fun x => CreatedObject.fromSomeObject x (ephemeral := false))
  let try destroyed : List SomeConsumedObject := funRes.destroyed.map (·.consume) |>.getSome
  let destroyedEph : List CreatedObject := destroyed.map (·.balanceDestroyed)
  let constructed : List CreatedObject := funRes.constructed.map (fun c => CreatedObject.fromSomeObject c false)
  let constructedEph : List SomeConsumedObject := funRes.constructed.map (·.balanceConstructed)
  let funData : FunctionData :=
    { numConstructed := constructed.length
      numDestroyed := destroyed.length
      numSelvesDestroyed := selvesDestroyedEph.length }
  let r ← Action.create lab (.functionId funId) funData fargs
          (consumed := consumedSelves.map Prod.snd ++ constructedEph ++ destroyed)
          (created := createdObjects ++ constructed ++ destroyedEph ++ selvesDestroyedEph)
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
    | {memberId := .classMember mem, memberArgs, ..} => Class.checkClassMemberLogic args eco mem memberArgs
    | {memberId := .functionId fn, memberArgs, memberData} => Function.logic eco args fn memberData memberArgs

def logic
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Anoma.Logic.Args SomeAppData) : Bool :=
  let try appData := tryCast args.data.appData
  logic' eco { args with data := appData }
