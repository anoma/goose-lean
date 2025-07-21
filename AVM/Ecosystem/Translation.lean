import AVM.Ecosystem
import Prelude
import AVM.Class.Translation
import AVM.Ecosystem.AppData
import AVM.Logic
import AVM.Action

namespace AVM.Ecosystem

open AVM.Action

/-- Creates a member logic for a given intent. This logic is checked when an
  object is consumed to create the intent. Note that the intent member logic
  (defined here) is distinct from the intent logic defined in
  `AVM/Intent/Translation.lean`. The intent member logic is associated with
  a resource consumed by the intent and it checks that the right intent is
  created. The intent logic is checked on consumption of the intent resource
  and it checks that the the intent's condition is satified. -/
def Intent.logic
  {lab : Ecosystem.Label}
  (intent : Intent)
  (args : Logic.Args lab)
  : Bool :=
  if args.isConsumed then
    -- Check that exactly one resource is created that corresponds to the intent
    match Logic.filterOutDummy args.created with
    | [intentRes] => BoolCheck.run do
      let labelData ← BoolCheck.some <| Intent.LabelData.fromResource intentRes
      BoolCheck.ret <|
        -- NOTE: We should also check that the intent logic hashes of
        -- `intentRes` and `intent` match.
        labelData.label === intent.label
        && intentRes.quantity == 1
        && intentRes.ephemeral
        && Logic.checkResourceData labelData.data.provided args.consumed
    | _ =>
      false
  else
    true

def Function.parseObjectArgs
  {lab : Ecosystem.Label}
  (args : Logic.Args lab)
  (funId : lab.FunctionId)
  : Option funId.Selves
  := do
  match args.consumed.toSizedVector with
  | none => none
  | some (consumedVec : Vector Anoma.Resource funId.numObjectArgs) =>
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
  match Function.parseObjectArgs args funId with
  | none => false
  | some (consumedObjects : funId.Selves) =>
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
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
  let fn : Function funId := eco.functions funId
  match Function.parseObjectArgs args funId with
  | none => pure none
  | some (consumedObjects : funId.Selves) =>
  let mconsumedList : Option (List SomeConsumedObject) :=
    (lab.objectArgNamesEnum funId).toList
    |>.map (fun arg =>
      (consumedObjects arg).toSomeObject
      |> SomeObject.toConsumable false (keys arg)
      |> SomeConsumableObject.consume)
    |>.getSome
  let createdObjects : List CreatedObject := fn.created consumedObjects fargs |>
      List.map (fun x => CreatedObject.fromSomeObject x (ephemeral := false)
        (nonce := Anoma.Nonce.todo)) -- FIXME the Nonce.todo should be replaced with the fix of https://github.com/anoma/goose-lean/issues/51
  match mconsumedList with
  | none => pure none
  | some (consumedList : List SomeConsumedObject) => do
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
    | {memberId := .intentId i, ..} => Intent.logic (eco.intents i) args
    | {memberId := .classMember mem, memberArgs} => Class.checkClassMemberLogic args eco mem memberArgs
    | {memberId := .functionId fn, memberArgs} => Function.logic eco args fn memberArgs

def logic
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Anoma.Logic.Args SomeAppData) : Bool :=
  match tryCast args.data.appData with
  | none => false
  | some appData =>
    logic' eco { args with data := appData }
