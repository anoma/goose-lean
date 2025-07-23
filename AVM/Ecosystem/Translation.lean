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
  (args : Logic.Args lab)
  (funId : lab.FunctionId)
  : Option funId.Selves
  :=
  let try consumedVec : Vector Anoma.Resource funId.numObjectArgs := args.consumed.toSizedVector
  let mkConsumedObject (a : funId.ObjectArgNames) : Option (Object a.classId.label) := Object.fromResource (consumedVec.get a.ix)
  match @FinEnum.decImageOption
        funId.ObjectArgNames
        (lab.objectArgNamesEnum funId)
        (fun a => Object a.classId.label)
        mkConsumedObject
  with
  -- there is at least one resource that cannot be decoded
  | .inr (_ : Σ (a : funId.ObjectArgNames), PLift (¬ (mkConsumedObject a).isSome)) => none
  | .inl (p : ∀ (a : funId.ObjectArgNames), PLift (mkConsumedObject a).isSome) =>
    pure fun (argName : funId.ObjectArgNames) =>
      match p1 : mkConsumedObject argName with
      | some obj => obj
      | none => by
            have c := (p argName).down
            rw [p1] at c
            contradiction

def Function.logic
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Logic.Args lab)
  (funId : lab.FunctionId)
  (fargs : funId.Args.type)
  : Bool :=
  let fn : Function funId := eco.functions funId
  let try consumedObjects : funId.Selves := Function.parseObjectArgs args funId
  let consumedList : List SomeObject :=
    List.map (fun arg => (consumedObjects arg).toSomeObject) (lab.objectArgNamesEnum funId).toList
  (eco.functions funId).invariant consumedObjects fargs
   && Logic.checkResourceData consumedList args.consumed
   && let createdObjects : List SomeObject := fn.created consumedObjects fargs
      Logic.checkResourceData createdObjects args.created

def Function.action
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Logic.Args lab)
  (funId : lab.FunctionId)
  (fargs : funId.Args.type)
  (keys : funId.ObjectArgNames → Anoma.NullifierKey)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) := do
  let fn : Function funId := eco.functions funId
  let try consumedObjects : funId.Selves := Function.parseObjectArgs args funId
  let try consumedList : List SomeConsumedObject :=
    (lab.objectArgNamesEnum funId).toList
    |>.map (fun arg =>
      (consumedObjects arg).toSomeObject
      |> SomeObject.toConsumable false (keys arg)
      |> SomeConsumableObject.consume)
    |>.getSome
  let createdObjects : List CreatedObject := fn.created consumedObjects fargs |>
      List.map (fun x => CreatedObject.fromSomeObject x (ephemeral := false))
  let r ← Action.create lab (.functionId funId) fargs consumedList createdObjects
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
