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
  resource : Anoma.Resource
  commitment : Anoma.Commitment

def CreatedObject.fromSomeObject (o : SomeObject) (ephemeral : Bool) (nonce : Anoma.Nonce) : CreatedObject :=
  let res : Anoma.Resource := o.toResource ephemeral nonce
  { object := o.object
    resource := res
    commitment := res.commitment }

def create'
  (g : StdGen)
  (lab : Ecosystem.Label)
  (memberId : lab.MemberId)
  (args : memberId.Args.type)
  (sconsumed : List SomeConsumedObject)
  (created : List CreatedObject) -- no appdata/logic
  : Anoma.Action × Anoma.DeltaWitness × StdGen :=
  let createdResources : List Anoma.Resource := created.map CreatedObject.resource
  let (createdWitnesses, g') : List Anoma.ComplianceWitness × StdGen :=
    createdResources.foldr mkCreatedComplianceWitness ([], g)
  let createdUnits : List Anoma.ComplianceUnit :=
    createdWitnesses.map Anoma.ComplianceUnit.create
  let logicVerifierInputs : Std.HashMap Anoma.Tag Anoma.LogicVerifierInput :=
    Std.HashMap.emptyWithCapacity
    |>.insertMany (List.map (Prod.map id (mkLogicVerifierInput Consumed) ∘ mkTagDataPairConsumed) sconsumed)
    |>.insertMany (List.map (Prod.map id (mkLogicVerifierInput Created) ∘ mkTagDataPairCreated) created)
  let (r, g'') := stdNext g'
  let mkConsumedWitness : SomeConsumedObject → Anoma.ComplianceWitness := fun ⟨c⟩ =>
      { consumedResource := c.resource
        createdResource := dummyResource c.can_nullify.nullifier.toNonce
        nfKey := c.key,
        rcv := r.repr }
  let consumedWitnesses := List.map mkConsumedWitness sconsumed
  let consumedUnits : List Anoma.ComplianceUnit := List.map Anoma.ComplianceUnit.create consumedWitnesses
  let action : Anoma.Action :=
    { complianceUnits := consumedUnits ++ createdUnits,
      logicVerifierInputs }
  let deltaWitness : Anoma.DeltaWitness :=
    Anoma.DeltaWitness.fromComplianceWitnesses (consumedWitnesses ++ createdWitnesses)
  (action, deltaWitness, g'')
  where
    mkCreatedComplianceWitness  (res : Anoma.Resource) : List Anoma.ComplianceWitness × StdGen → List Anoma.ComplianceWitness × StdGen
      | (acc, g) =>
        let (r, g') := stdNext g
        let (r', g'') := stdNext g'
        let complianceWitness :=
            { consumedResource := dummyResource ⟨r⟩
              createdResource := res
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
            memberArgs := args }})

    mkTagDataPairCreated (i : CreatedObject)
     : Anoma.Tag × SomeAppData :=
      (Anoma.Tag.Created i.commitment,
        { label := lab,
          appData := {
            memberId := .falseLogicId,
            memberArgs := UUnit.unit }})

/-- Helper function to create an Action. -/
def create
  (lab : Ecosystem.Label)
  (memberId : lab.MemberId)
  (args : memberId.Args.type)
  (consumed : List SomeConsumedObject)
  (created : List CreatedObject) -- no appdata/logic
  : Rand (Anoma.Action × Anoma.DeltaWitness) := do
  let g ← get
  let (action, witness, g') := Action.create' g.down lab memberId args consumed created
  set (ULift.up g')
  return (action, witness)
