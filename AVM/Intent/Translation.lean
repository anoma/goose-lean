import Prelude
import Mathlib.Control.Random
import AVM.Intent
import AVM.Class.Label
import AVM.Logic
import AVM.Object.Consumed

namespace AVM

/-- The intent logic which is checked when the intent resource is consumed. The
  intent logic checks the intent's condition. -/
def Intent.logic {ilab : Intent.Label} (intent : Intent ilab) (args : Anoma.Logic.Args Unit) : Bool :=
  if args.isConsumed then
    let try data := Intent.ResourceData.fromResource args.self
    let try receivedObjects :=
        List.mapSome SomeObject.fromResource <|
        Logic.filterOutDummy args.created
    let try argsData := tryCast data.args
    intent.condition argsData data.provided receivedObjects
  else
    -- In the created case, we need to check that the list of provided objects
    -- corresponds to the list consumed resources. See:
    -- https://github.com/anoma/goose-lean/issues/32.
    let try data := Intent.ResourceData.fromResource args.self
    Logic.checkResourcesData (data.provided.map SomeObject.toSomeObjectData) args.consumed

/-- An action which consumes the provided objects and creates the intent. This
  is a helper function which handles the random number generator explicitly to
  avoid universe level inconsistencies with monadic notation. -/
def Intent.action'
  {ilab : Intent.Label}
  (g : StdGen)
  (intent : Intent ilab)
  (args : ilab.Args.type)
  (provided : List SomeObject)
  : Option (Anoma.Action × Anoma.DeltaWitness) × StdGen :=
  let try providedConsumed :=
        provided.map (fun p => p.toConsumable false |>.consume) |>.getSome
      failwith (none, g)
  let logicVerifierInputs : Std.HashMap Anoma.Tag Anoma.LogicVerifierInput := ∅
  let (consumedWitnesses, g1) : List Anoma.ComplianceWitness × StdGen :=
    providedConsumed.foldr mkConsumedComplianceWitness ([], g)
  let consumedUnits : List Anoma.ComplianceUnit :=
    consumedWitnesses.map Anoma.ComplianceUnit.create
  let (r1, g2) := stdNext g1
  let (r2, g3) := stdNext g2
  let res := Action.dummyResource ⟨r1⟩
  let can_nullify := res.nullifyUniversal
  let nonce := can_nullify.nullifier.toNonce
  let intentResource : Anoma.Resource := Intent.toResource intent args provided nonce
  let createdWitness : Anoma.ComplianceWitness :=
    { consumedResource := res,
      createdResource := intentResource,
      nfKey := Anoma.NullifierKey.universal,
      rcv := r2.repr }
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
        { consumedResource := obj.consumed.toResource,
          createdResource := Action.dummyResource obj.consumed.can_nullify.nullifier.toNonce,
          nfKey := Anoma.NullifierKey.universal
          rcv := r.repr }
      (complianceWitness :: acc, g')

/-- An action which consumes the provided objects and creates the intent. -/
def Intent.action
  {ilab : Intent.Label}
  (intent : Intent ilab)
  (args : ilab.Args.type)
  (provided : List SomeObject)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) := do
  let g ← get
  let (p, g') := Intent.action' g.down intent args provided
  set (ULift.up g')
  pure p

/-- A (partial) transaction which consumes the provided objects and creates the
  intent. -/
def Intent.transaction
  {ilab : Intent.Label}
  (intent : Intent ilab)
  (args : ilab.Args.type)
  (provided : List SomeObject)
  : Rand (Option Anoma.Transaction) := do
  let try (action, witness) ← intent.action args provided
  pure <|
    some
      { actions := [action],
        deltaProof := Anoma.Transaction.generateDeltaProof witness [action] }
