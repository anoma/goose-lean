import Prelude
import Mathlib.Control.Random
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
def Intent.logic {ilab : Intent.Label} (intent : Intent ilab) (args : Anoma.Logic.Args Unit) : Bool :=
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

/-- An action which consumes the provided objects and creates the intent. This
  is a helper function which handles the random number generator explicitly to
  avoid universe level inconsistencies with monadic notation. -/
def Intent.action'
  (label : Ecosystem.Label)
  {ilab : Intent.Label}
  (g : StdGen)
  (intent : Intent ilab)
  (args : ilab.Args.type)
  (provided : List SomeObject)
  (key : Anoma.NullifierKey)
  : Option (Anoma.Action × Anoma.DeltaWitness) × StdGen :=
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
      let (consumedWitnesses, g1) : List Anoma.ComplianceWitness × StdGen :=
        providedConsumed.foldr mkConsumedComplianceWitness ([], g)
      let consumedUnits : List Anoma.ComplianceUnit :=
        consumedWitnesses.map Anoma.ComplianceUnit.create
      let (r, g2) := stdNext g1
      let (r', g3) := stdNext g2
      let createdWitness : Anoma.ComplianceWitness :=
        { consumedResource := dummyResource ⟨r⟩,
          createdResource := intentResource,
          nfKey := key,
          rcv := r'.repr }
      let createdUnit : Anoma.ComplianceUnit :=
        Anoma.ComplianceUnit.create createdWitness
      let action :=
          { complianceUnits := consumedUnits ++ [createdUnit],
            logicVerifierInputs }
      let witness : Anoma.DeltaWitness :=
        Anoma.DeltaWitness.fromComplianceWitnesses (consumedWitnesses ++ [createdWitness])
      (some (action, witness), g3)
    where
      mkConsumedComplianceWitness (obj : SomeConsumedObject) : List Anoma.ComplianceWitness × StdGen → List Anoma.ComplianceWitness × StdGen
        | (acc, g) =>
          let (r, g') := stdNext g
          let complianceWitness :=
            { consumedResource := obj.consumed.resource,
              createdResource := dummyResource obj.consumed.can_nullify.nullifier.toNonce,
              nfKey := obj.consumed.key
              rcv := r.repr }
          (complianceWitness :: acc, g')

      mkLogicVerifierInput (status : ConsumedCreated) (data : SomeAppData) : Anoma.LogicVerifierInput :=
        { Data := ⟨SomeAppData⟩,
          status,
          appData := data }

      mkTagDataPairConsumed (c : SomeConsumedObject)
       : Option (Anoma.Tag × SomeAppData) :=
        match label.classId c.label with
        | none => none
        | some classId =>
          some
            (Anoma.Tag.Consumed c.consumed.can_nullify.nullifier,
              { label := label,
                appData := {
                  memberId := .classMember (classId := classId) (Class.Label.MemberId.intentId ilab),
                  memberArgs := UUnit.unit }})

/-- An action which consumes the provided objects and creates the intent. -/
def Intent.action
  (lab : Ecosystem.Label)
  {ilab : Intent.Label}
  (intent : Intent ilab)
  (args : ilab.Args.type)
  (provided : List SomeObject)
  (key : Anoma.NullifierKey)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) := do
  let g ← get
  let (p, g') := Intent.action' lab g.down intent args provided key
  set (ULift.up g')
  pure p

/-- A (partial) transaction which consumes the provided objects and creates the
  intent. -/
def Intent.transaction
  (label : Ecosystem.Label)
  {ilab : Intent.Label}
  (intent : Intent ilab)
  (args : ilab.Args.type)
  (provided : List SomeObject)
  (key : Anoma.NullifierKey)
  : Rand (Option Anoma.Transaction) := do
  match ← intent.action label args provided key with
  | none => pure none
  | some (action, witness) =>
    pure <|
      some
        { actions := [action],
          deltaProof := Anoma.Transaction.generateDeltaProof witness [action] }
