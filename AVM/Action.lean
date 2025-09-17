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

def CreatedObject.toObject (c : CreatedObject) : Object c.classId :=
  let res : Anoma.Resource := Action.dummyResource.{0, 0} ⟨c.rand⟩
  let nonce := res.nullifyUniversal.nullifier.toNonce
  {uid := c.uid, nonce, data := c.data}

def CreatedObject.toResource (c : CreatedObject) : Anoma.Resource :=
  c.toObject.toResource (ephemeral := c.ephemeral)

def Action.create'
  (g : StdGen)
  (consumedObjects : List SomeConsumedObject)
  (createdObjects : List CreatedObject)
  (ensureUnique : List Anoma.Nonce)
  (consumedMessages : List SomeMessage)
  (createdMessages : List SomeMessage)
  : Anoma.Action.{u} × Anoma.DeltaWitness × StdGen :=
  let (createdWitnesses, g') : List Anoma.ComplianceWitness × StdGen :=
    ([], g) |>
    createdObjects.foldr mkCreatedComplianceWitness |>
    ensureUnique.foldr mkDummyComplianceWitness |>
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

    mkCreatedResourceComplianceWitness (created : Anoma.Resource) (consumedNonce : Anoma.Nonce) : List Anoma.ComplianceWitness × StdGen → List Anoma.ComplianceWitness × StdGen
      | (acc, g) =>
        let (r, g') := stdNext g
        let consumed := dummyResource consumedNonce
        let complianceWitness :=
            { consumedResource := consumed
              createdResource := created
              nfKey := Anoma.NullifierKey.universal,
              rcv := r.repr }
        (complianceWitness :: acc, g')

    mkDummyComplianceWitness (nonce : Anoma.Nonce) : List Anoma.ComplianceWitness × StdGen → List Anoma.ComplianceWitness × StdGen
      | (acc, g) =>
        let (r, g') := stdNext g
        mkCreatedResourceComplianceWitness (dummyResource nonce) (Anoma.Nonce.mk r) (acc, g')

    mkCreatedComplianceWitness (obj : CreatedObject) : List Anoma.ComplianceWitness × StdGen → List Anoma.ComplianceWitness × StdGen :=
      mkCreatedResourceComplianceWitness obj.toResource (Anoma.Nonce.mk obj.rand)

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
  (ensureUnique : List Anoma.Nonce)
  (consumedMessages : List SomeMessage)
  (createdMessages : List SomeMessage)
  : Rand (Anoma.Action × Anoma.DeltaWitness) := do
  let g ← get
  let (action, witness, g') := Action.create' g.down consumedObjects createdObjects ensureUnique consumedMessages createdMessages
  set (ULift.up g')
  return (action, witness)

/-- Used to balance a consumed object that's meant to be destroyed -/
def SomeConsumableObject.balanceDestroyed (rand : Nat) (destroyed : SomeConsumableObject) : CreatedObject where
  uid := destroyed.consumable.object.uid
  data := destroyed.consumable.object.data
  ephemeral := true
  rand

/-- Used to balance a constructed object -/
def SomeObject.balanceConstructed (constructed : SomeObject) : SomeConsumableObject where
  label := constructed.label
  classId := constructed.classId
  consumable :=
    let obj : Object constructed.classId := constructed.object
    { object := obj,
      ephemeral := true }
