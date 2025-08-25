import Mathlib.Control.Random
import Prelude
import Anoma
import AVM.Class
import AVM.Class.Label
import AVM.Ecosystem
import AVM.Object
import AVM.Object.Consumable
import AVM.Class.Member
import AVM.Logic

namespace AVM.Action

structure CreatedObject where
  {label : Class.Label}
  object : Object label
  ephemeral : Bool

def CreatedObject.fromSomeObject (o : SomeObject) (ephemeral : Bool) : CreatedObject :=
  { object := o.object
    ephemeral }

def CreatedObject.resource (c : CreatedObject) (nonce : Anoma.Nonce) : Anoma.Resource :=
  Object.toResource c.object (ephemeral := c.ephemeral) nonce

def create'
  (g : StdGen)
  (lab : Ecosystem.Label)
  (memberId : lab.MemberId)
  (memberData : memberId.Data)
  (args : memberId.Args.type)
  (sconsumed : List SomeConsumedObject)
  (created : List CreatedObject) -- no appdata/logic
  : Anoma.Action × Anoma.DeltaWitness × StdGen :=
  let (createdWitnesses, g') : List Anoma.ComplianceWitness × StdGen :=
    created.foldr mkCreatedComplianceWitness ([], g)
  let createdUnits : List Anoma.ComplianceUnit :=
    createdWitnesses.map Anoma.ComplianceUnit.create
  let createdResources : List Anoma.Resource :=
    createdWitnesses.map Anoma.ComplianceWitness.createdResource
  let logicVerifierInputs : Std.HashMap Anoma.Tag Anoma.LogicVerifierInput :=
    Std.HashMap.emptyWithCapacity
    |>.insertMany (List.map (Prod.map id (mkLogicVerifierInput Consumed) ∘ mkTagDataPairConsumed) sconsumed)
    |>.insertMany (List.map (Prod.map id (mkLogicVerifierInput Created) ∘ mkTagDataPairCreated) createdResources)
  let (consumedWitnesses, g'') := List.foldr mkConsumedComplianceWitness ([], g') sconsumed
  let consumedUnits : List Anoma.ComplianceUnit := List.map Anoma.ComplianceUnit.create consumedWitnesses
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
          { consumedResource := c.resource,
            createdResource := dummyResource c.can_nullify.nullifier.toNonce,
            nfKey := Anoma.NullifierKey.universal,
            rcv := r.repr }
        (witness :: acc, g')
    mkCreatedComplianceWitness  (obj : CreatedObject) : List Anoma.ComplianceWitness × StdGen → List Anoma.ComplianceWitness × StdGen
      | (acc, g) =>
        let (r, g') := stdNext g
        let (r', g'') := stdNext g'
        let res := dummyResource ⟨r⟩
        let can_nullify := Anoma.nullifyUniversal res
        let nonce := can_nullify.nullifier.toNonce
        let complianceWitness :=
            { consumedResource := res
              createdResource := obj.resource nonce
              nfKey := Anoma.NullifierKey.universal,
              rcv := r'.repr }
        (complianceWitness :: acc, g'')

    mkLogicVerifierInput (status : ConsumedCreated) (data : SomeAppData) : Anoma.LogicVerifierInput :=
      { Data := ⟨SomeAppData⟩,
        status,
        appData := data }

    mkTagDataPairConsumed : SomeConsumedObject → Anoma.Tag × SomeAppData :=
     fun ⟨c⟩ =>
      (Anoma.Tag.Consumed c.can_nullify.nullifier,
        { appData := {
            memberId := memberId,
            memberData,
            memberArgs := args }})

    mkTagDataPairCreated (r : Anoma.Resource)
     : Anoma.Tag × SomeAppData :=
      (Anoma.Tag.Created r.commitment,
        { label := lab,
          appData := {
            memberId := .falseLogicId,
            memberData := PUnit.unit,
            memberArgs := PUnit.unit }})

/-- Helper function to create an Action. -/
def create
  (lab : Ecosystem.Label)
  (memberId : lab.MemberId)
  (memberData : memberId.Data)
  (args : memberId.Args.type)
  (consumed : List SomeConsumedObject)
  (created : List CreatedObject) -- no appdata/logic
  : Rand (Anoma.Action × Anoma.DeltaWitness) := do
  let g ← get
  let (action, witness, g') := Action.create' g.down lab memberId memberData args consumed created
  set (ULift.up g')
  return (action, witness)

end Action

/-- Used to balance a consumed object that's meant to be destroyed -/
def SomeConsumedObject.balanceDestroyed (destroyed : SomeConsumedObject) : Action.CreatedObject where
  object := destroyed.consumed.object
  ephemeral := true

/-- Used to balance a constructed object -/
def SomeObject.balanceConstructed (constructed : SomeObject) : SomeConsumedObject where
  consumed :=
  let obj : Object constructed.label := constructed.object
  { object := obj,
    can_nullify := Anoma.nullifyUniversal (obj.toResource true obj.nonce.get!)
    ephemeral := true }
