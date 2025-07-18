import Prelude
import AVM.Intent
import AVM.Class.Label
import AVM.Logic
import AVM.Ecosystem
import AVM.Ecosystem.AppData
import AVM.Object.Consumable

namespace AVM

open Ecosystem

/-- The intent logic which is checked when the intent resource is consumed. The
  intent logic checks the intent's condition. -/
def Intent.logic (intent : Intent) (args : Anoma.Logic.Args Unit) : Bool :=
  if args.isConsumed then
    BoolCheck.run do
      let data ← BoolCheck.some <| Intent.ResourceData.fromResource args.self
      let receivedObjects ←
        BoolCheck.some <|
          List.mapSome SomeObject.fromResource <|
          Logic.filterOutDummy args.created
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
        Logic.checkResourceData data.provided args.consumed

/-- An action which consumes the provided objects and creates the intent. -/
def Intent.action (label : EcosystemLabel) (intent : Intent) (args : intent.Args.type) (provided : List SomeObject) (key : Anoma.NullifierKey) : Option Anoma.Action := do
  -- TODO: set nonce properly
  let intentResource := Intent.toResource intent args provided
  match provided.map (fun p => p.toConsumable false key |>.consume) |>.getSome with
  | none => none
  | some providedConsumed =>
    match providedConsumed.map mkTagDataPairConsumed |>.getSome with
    | none => none
    | some appDataPairs =>
      let logicVerifierInputs : Std.HashMap Anoma.Tag Anoma.LogicVerifierInput :=
        Std.HashMap.emptyWithCapacity
        |>.insertMany (appDataPairs.map (fun (tag, data) => (tag, mkLogicVerifierInput Consumed data)))
      let consumedUnits : List Anoma.ComplianceUnit :=
        providedConsumed.map (fun obj =>
          Anoma.ComplianceUnit.create
            { consumedResource := obj.consumed.resource,
              createdResource := dummyResource,
              nfKey := obj.consumed.key })
      let createdUnit : Anoma.ComplianceUnit :=
        Anoma.ComplianceUnit.create
          { consumedResource := dummyResource,
            createdResource := intentResource,
            nfKey := key }
      some
        { complianceUnits := consumedUnits ++ [createdUnit],
          logicVerifierInputs }
    where
      mkLogicVerifierInput (status : ConsumedCreated) (data : SomeAppData) : Anoma.LogicVerifierInput :=
        { Data := ⟨SomeAppData⟩,
          status,
          appData := data }

      mkTagDataPairConsumed (c : SomeConsumedObject)
       : Option (Anoma.Tag × SomeAppData) :=
        match EcosystemLabel.IntentId.fromIntentLabel (lab := label) intent.label with
        | none => none
        | some intentId =>
          some
            (Anoma.Tag.Consumed c.consumed.nullifierProof.nullifier,
              { label := label,
                appData :=
                 { memberId := intentId,
                   memberArgs := UUnit.unit }})

/-- A transaction which consumes the provided objects and creates the intent. -/
def Intent.transaction (label : EcosystemLabel) (intent : Intent) (args : intent.Args.type) (provided : List SomeObject) (key : Anoma.NullifierKey) : Option Anoma.Transaction := do
  let action ← intent.action label args provided key
  some
    { actions := [action],
      -- TODO: set deltaProof properly
      deltaProof := "" }
