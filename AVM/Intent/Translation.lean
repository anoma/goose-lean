
import Prelude
import AVM.Intent
import AVM.Class.Member.Logic
import AVM.Class.AppData
import AVM.Object.Consumable

namespace AVM

/-- The intent logic which is checked when the intent resource is consumed. The
  intent logic checks the intent's condition. -/
def Intent.logic (intent : Intent) (args : Anoma.Logic.Args Unit) : Bool :=
  if args.isConsumed then
    BoolCheck.run do
      let data ← BoolCheck.some <| Intent.ResourceData.fromResource args.self
      -- We use fake values for public fields of created objects. Public fields
      -- for created resources are not available, because they are stored in app
      -- data and in RL arguments app data is available only for the `self`
      -- resource.
      let receivedObjects ← BoolCheck.some <| List.mapSome (SomeObject.fromResource (PublicFields := ⟨Unit⟩) ()) args.created
      let argsData ← BoolCheck.some <| tryCast data.args
      BoolCheck.ret <|
        intent.condition argsData data.provided receivedObjects
  else
    -- In the created case, we need to check that the list of provided objects
    -- corresponds to the list consumed resources. See:
    -- https://github.com/anoma/goose-lean/issues/32.
    BoolCheck.run do
      let data ← BoolCheck.some <| Intent.ResourceData.fromResource args.self
      BoolCheck.ret <|
        Class.Member.Logic.checkResourceData data.provided args.consumed

/-- An action which consumes the provided objects and creates the intent. -/
def Intent.action (intent : Intent) (args : intent.Args.type) (provided : List SomeObject) (key : Anoma.NullifierKey) : Option Anoma.Action := do
  -- TODO: set nonce properly
  let intentResource := Intent.toResource intent args provided
  match (List.map (fun p => (p.toConsumable false key).consume) provided).getSome with
  | none => none
  | some providedConsumed =>
    match (List.map mkTagDataPairConsumed providedConsumed).getSome with
    | none => none
    | some appDataPairs =>
      let appData : Std.HashMap Anoma.Tag Class.SomeAppData :=
        Std.HashMap.emptyWithCapacity
        |>.insertMany appDataPairs
      some
        { Data := ⟨Class.SomeAppData⟩,
          consumed := List.map SomeConsumedObject.toRootedNullifiableResource providedConsumed,
          created := [intentResource],
          appData }
    where
      mkTagDataPairConsumed (c : SomeConsumedObject)
       : Option (Anoma.Tag × Class.SomeAppData) :=
        match Class.Label.IntentId.fromIntentLabel (lab := c.label) intent.label with
        | none => none
        | some intentId =>
          some
            (Anoma.Tag.Consumed c.consumed.nullifierProof.nullifier,
              { label := c.label,
                appData := {
                  memberId := Class.Label.MemberId.intentId intentId,
                  memberArgs := UUnit.unit,
                  publicFields := c.consumed.object.publicFields }})

/-- A transaction which consumes the provided objects and creates the intent. -/
def Intent.transaction (intent : Intent) (args : intent.Args.type) (provided : List SomeObject) (key : Anoma.NullifierKey) (currentRoot : Anoma.CommitmentRoot) : Option Anoma.Transaction := do
  let action ← intent.action args provided key
  some
    { roots := [currentRoot],
      actions := [action],
      -- TODO: set deltaProof properly
      deltaProof := "" }
