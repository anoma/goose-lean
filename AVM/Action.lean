import Mathlib.Control.Random
import Prelude
import Anoma
import AVM.Class
import AVM.Class.Label
import AVM.Object
import AVM.Object.Consumed
import AVM.Object.Created
import AVM.Class.Member
import AVM.Logic
import AVM.Message

namespace AVM

def CreatedObject.toObject (c : CreatedObject.{u}) : Object c.label :=
  let res : Anoma.Resource.{u, u} := Action.dummyResource ⟨c.rand⟩
  let nonce := res.nullifyUniversal.nullifier.toNonce
  {uid := c.uid, nonce, data := c.data}

def CreatedObject.toResource (c : CreatedObject) : Anoma.Resource :=
  c.toObject.toResource (ephemeral := c.ephemeral)

def Action.create'
  (g : StdGen)
  (consumedObjects : List SomeConsumedObject)
  (createdObjects : List CreatedObject)
  (consumedMessages : List SomeMessage)
  (createdMessages : List SomeMessage)
  : Anoma.Action.{u} × Anoma.DeltaWitness × StdGen :=
  let (createdWitnesses, g') : List Anoma.ComplianceWitness × StdGen :=
    ([], g) |>
    createdObjects.foldr mkCreatedComplianceWitness |>
    createdMessages.foldr mkCreatedMessageComplianceWitness
  let createdUnits : List Anoma.ComplianceUnit :=
    createdWitnesses.map Anoma.ComplianceUnit.create
  let (consumedWitnesses, g'') : List Anoma.ComplianceWitness × StdGen :=
    ([], g') |>
    consumedObjects.foldr mkConsumedComplianceWitness |>
    consumedMessages.foldr mkConsumedMessageComplianceWitness
  let consumedUnits : List Anoma.ComplianceUnit := List.map Anoma.ComplianceUnit.create consumedWitnesses
  let logicVerifierInputs : Std.HashMap Anoma.Tag Anoma.LogicVerifierInput := ∅
  let action : Anoma.Action :=
    { complianceUnits := consumedUnits ++ createdUnits,
      logicVerifierInputs }
  let deltaWitness : Anoma.DeltaWitness :=
    Anoma.DeltaWitness.fromComplianceWitnesses (consumedWitnesses ++ createdWitnesses)
  (action, deltaWitness, g'')
  where
    mkConsumedComplianceWitness : SomeConsumedObject → List Anoma.ComplianceWitness × StdGen → List Anoma.ComplianceWitness × StdGen
      | ⟨c⟩, (acc, g) =>
        let (r, g') := stdNext g
        let witness :=
          { consumedResource := c.toResource,
            createdResource := dummyResource c.can_nullify.nullifier.toNonce,
            nfKey := Anoma.NullifierKey.universal,
            rcv := r.repr }
        (witness :: acc, g')

    mkCreatedComplianceWitness (obj : CreatedObject) : List Anoma.ComplianceWitness × StdGen → List Anoma.ComplianceWitness × StdGen
      | (acc, g) =>
        let (r, g') := stdNext g
        let res := dummyResource ⟨obj.rand⟩
        let nonce := res.nullifyUniversal.nullifier.toNonce
        let complianceWitness :=
            { consumedResource := res
              createdResource := obj.toResource
              nfKey := Anoma.NullifierKey.universal,
              rcv := r.repr }
        (complianceWitness :: acc, g')

    mkConsumedMessageComplianceWitness (msg : SomeMessage) : List Anoma.ComplianceWitness × StdGen → List Anoma.ComplianceWitness × StdGen
      | (acc, g) =>
        let (r, g') := stdNext g
        let (r', g'') := stdNext g'
        let res := msg.toResource ⟨r⟩
        let witness :=
          { consumedResource := res,
            createdResource := dummyResource res.nullifyUniversal.nullifier.toNonce,
            nfKey := Anoma.NullifierKey.universal,
            rcv := r'.repr }
        (witness :: acc, g'')

    mkCreatedMessageComplianceWitness (msg : SomeMessage) : List Anoma.ComplianceWitness × StdGen → List Anoma.ComplianceWitness × StdGen
      | (acc, g) =>
        let (r, g') := stdNext g
        let (r', g'') := stdNext g'
        let res := dummyResource ⟨r⟩
        let nonce := res.nullifyUniversal.nullifier.toNonce
        let complianceWitness :=
            { consumedResource := res
              createdResource := msg.toResource nonce
              nfKey := Anoma.NullifierKey.universal,
              rcv := r'.repr }
        (complianceWitness :: acc, g'')

/-- Helper function to create an Action. The nonces of created objects are
  set to the nullifiers of the consumed dummy resources from corresponding
  compliance units. The nonces of consumed objects are preserved. -/
def Action.create
  (consumedObjects : List SomeConsumedObject)
  (createdObjects : List CreatedObject)
  (consumedMessages : List SomeMessage)
  (createdMessages : List SomeMessage)
  : Rand (Anoma.Action × Anoma.DeltaWitness) := do
  let g ← get
  let (action, witness, g') := Action.create' g.down consumedObjects createdObjects consumedMessages createdMessages
  set (ULift.up g')
  return (action, witness)

/-- Used to balance a consumed object that's meant to be destroyed -/
def SomeConsumedObject.balanceDestroyed (rand : Nat) (destroyed : SomeConsumedObject) : CreatedObject where
  uid := destroyed.consumed.object.uid
  data := destroyed.consumed.object.data
  ephemeral := true
  rand

/-- Used to balance a constructed object -/
def SomeObject.balanceConstructed (constructed : SomeObject) : SomeConsumedObject where
  consumed :=
  let obj : Object constructed.label := constructed.object
  { object := obj,
    can_nullify := Anoma.Resource.nullifyUniversal (obj.toResource true)
    ephemeral := true }
