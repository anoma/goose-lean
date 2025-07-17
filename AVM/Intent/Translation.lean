
import Prelude
import Mathlib.Control.Random
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
      let receivedObjects ←
        BoolCheck.some <|
          List.mapSome SomeObject.fromResource <|
          Class.Member.Logic.filterOutDummy args.created
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

/-- An action which consumes the provided objects and creates the intent. Helper
  function which handles the random number generator explicitly to avoid
  universe level inconsistencies with monadic notation. -/
def Intent.action' (g : StdGen)
  (intent : Intent)
  (args : intent.Args.type)
  (provided : List SomeObject)
  (key : Anoma.NullifierKey)
  : Option Anoma.Action × StdGen :=
  -- TODO: set nonce properly
  let intentResource := Intent.toResource intent args provided
  match provided.map (fun p => p.toConsumable false key |>.consume) |>.getSome with
  | none => (none, g)
  | some providedConsumed =>
    match providedConsumed.map mkTagDataPairConsumed |>.getSome with
    | none => (none, g)
    | some appDataPairs =>
      let logicVerifierInputs : Std.HashMap Anoma.Tag Anoma.LogicVerifierInput :=
        Std.HashMap.emptyWithCapacity
        |>.insertMany (appDataPairs.map (fun (tag, data) => (tag, mkLogicVerifierInput Consumed data)))
      let consumedUnits : List Anoma.ComplianceUnit :=
        providedConsumed.map (fun obj =>
          Anoma.ComplianceUnit.create
            { consumedResource := obj.consumed.resource,
              createdResource := Class.dummyResource obj.consumed.can_nullify.nullifier.toNonce,
              nfKey := obj.consumed.key })
      let (r, g') := stdNext g
      let createdUnit : Anoma.ComplianceUnit :=
        Anoma.ComplianceUnit.create
          { consumedResource := Class.dummyResource r,
            createdResource := intentResource,
            nfKey := key }
      let action :=
          { complianceUnits := consumedUnits ++ [createdUnit],
            logicVerifierInputs }
      (some action, g')
    where
      mkLogicVerifierInput (status : ConsumedCreated) (data : Class.SomeAppData) : Anoma.LogicVerifierInput :=
        { Data := ⟨Class.SomeAppData⟩,
          status,
          appData := data }

      mkTagDataPairConsumed (c : SomeConsumedObject)
       : Option (Anoma.Tag × Class.SomeAppData) :=
        match Class.Label.IntentId.fromIntentLabel (lab := c.label) intent.label with
        | none => none
        | some intentId =>
          some
            (Anoma.Tag.Consumed c.consumed.can_nullify.nullifier,
              { label := c.label,
                appData := {
                  memberId := Class.Label.MemberId.intentId intentId,
                  memberArgs := UUnit.unit }})

/-- An action which consumes the provided objects and creates the intent. -/
def Intent.action (intent : Intent)
  (args : intent.Args.type)
  (provided : List SomeObject)
  (key : Anoma.NullifierKey)
  : Rand (Option Anoma.Action) := do
  let g ← get
  let (action, g') := Intent.action' g.down intent args provided key
  set (ULift.up g')
  pure action

/-- A transaction which consumes the provided objects and creates the intent. -/
def Intent.transaction (intent : Intent)
  (args : intent.Args.type)
  (provided : List SomeObject)
  (key : Anoma.NullifierKey)
  : Rand (Option Anoma.Transaction) := do
  match ← intent.action args provided key with
  | none => pure none
  | some action =>
    pure <|
      some
        { actions := [action],
          -- TODO: set deltaProof properly
          deltaProof := "" }
