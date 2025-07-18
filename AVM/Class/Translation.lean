
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

namespace AVM.Ecosystem

open Ecosystem

structure CreatedObject where
  {label : Class.Label}
  object : Object label
  resource : Anoma.Resource
  commitment : Anoma.Commitment

def CreatedObject.fromSomeObject (o : SomeObject) (ephemeral : Bool) : CreatedObject :=
  let res : Anoma.Resource := o.toResource ephemeral
  { object := o.object
    resource := res
    commitment := res.commitment }

def Action.create
  (g : StdGen)
  (lab : EcosystemLabel)
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
    |>.insertMany [Prod.map id (mkLogicVerifierInput Consumed) (mkTagDataPairConsumed consumed)]
    |>.insertMany (List.map (Prod.map id (mkLogicVerifierInput Created) ∘ mkTagDataPairCreated) created)
  let consumedResource : Anoma.Resource := consumed.resource
  let (r, g'') := stdNext g'
  let consumedWitness : Anoma.ComplianceWitness :=
      { consumedResource := consumedResource
        createdResource := dummyResource consumed.can_nullify.nullifier.toNonce
        nfKey := consumed.key,
        rcv := r.repr }
  let consumedUnit : Anoma.ComplianceUnit :=
    Anoma.ComplianceUnit.create consumedWitness
  let action : Anoma.Action :=
    { complianceUnits := consumedUnit :: createdUnits,
      logicVerifierInputs }
  let deltaWitness : Anoma.DeltaWitness :=
    Anoma.DeltaWitness.fromComplianceWitnesses (consumedWitness :: createdWitnesses)
  (action, deltaWitness, g'')
  where
    mkCreatedComplianceWitness  (res : Anoma.Resource) : List Anoma.ComplianceWitness × StdGen → List Anoma.ComplianceWitness × StdGen
      | (acc, g) =>
        let (r, g') := stdNext g
        let (r', g'') := stdNext g'
        let complianceWitness :=
            { consumedResource := dummyResource r
              createdResource := res
              nfKey := Anoma.NullifierKey.universal,
              rcv := r'.repr }
        (complianceWitness :: acc, g'')

    mkLogicVerifierInput (status : ConsumedCreated) (data : Class.SomeAppData) : Anoma.LogicVerifierInput :=
      { Data := ⟨Class.SomeAppData⟩,
        status,
        appData := data }

    mkTagDataPairConsumed (i : ConsumedObject lab)
     : Anoma.Tag × Class.SomeAppData :=
      (Anoma.Tag.Consumed i.can_nullify.nullifier,
        { appData := {
            memberId := memberId,
            memberArgs := args }})

    mkTagDataPairCreated (i : CreatedObject)
     : Anoma.Tag × SomeAppData :=
      (Anoma.Tag.Created i.commitment,
        { label := i.label,
          appData := {
            memberId := Label.MemberId.falseLogicId,
            memberArgs := UUnit.unit }})

/-- Helper function to create an Action. -/
private def Action.create
  (lab : Label)
  (memberId : Label.MemberId lab)
  (args : memberId.Args.type)
  (consumed : ConsumedObject lab)
  (created : List CreatedObject) -- no appdata/logic
  : Rand (Anoma.Action × Anoma.DeltaWitness) := do
  let g ← get
  let (action, witness, g') := Action.create' g.down lab memberId args consumed created
  set (ULift.up g')
  return (action, witness)

/-- Creates a logic for a given constructor. This logic is combined with other
    method and constructor logics to create the complete resource logic for an
    object. -/
def Constructor.logic
  {lab : EcosystemLabel}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor constrId)
  (args : Logic.Args lab)
  : Bool :=
    if args.isConsumed then
      match SomeType.cast args.data.memberArgs with
      | some argsData =>
        let newObj := constr.created argsData
        Logic.checkResourceData [newObj.toSomeObject] args.consumed
          && Logic.checkResourceData [newObj.toSomeObject] args.created
          && constr.invariant argsData
      | none =>
        false
    else
      -- TODO: not general enough, fine for the counter
      true

def Constructor.action
  {lab : EcosystemLabel}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor constrId)
  (args : constrId.Args.type)
  : Rand (Anoma.Action × Anoma.DeltaWitness) :=
    -- TODO: set nonce properly
    let clab := classId.label
    let newObj : Object clab := constr.created args
    let consumable : ConsumableObject clab :=
       { object := {newObj with nullifierKeyCommitment := Anoma.NullifierKeyCommitment.universal}
         ephemeral := true
         key := Anoma.NullifierKey.universal }
    let consumed : ConsumedObject lab := { consumable with can_nullify := Anoma.nullifyUniversal consumable.resource consumable.key rfl rfl }
    let createdResource : Anoma.Resource := newObj.toSomeObject.toResource (ephemeral := false) (nonce := consumed.can_nullify.nullifier.toNonce)
    let created : List CreatedObject :=
          [CreatedObject.fromSomeObject (newObj.toSomeObject) (ephemeral := false)]
    Action.create lab classId constrId args [consumed] created

/-- Creates an Anoma Transaction for a given object construtor. -/
def Constructor.transaction
  {lab : EcosystemLabel}
  {classId : lab.ClassId}
  {constrId : calssId.label.ConstructorId}
  (constr : Class.Constructor constrId) (args : constrId.Args.type)
  : Rand Anoma.Transaction := do
    let (action, witness) ← constr.action args
    pure <|
      { actions := [action],
        -- TODO: automatically generate deltaProof that verifies that the transaction is balanced
        deltaProof := Anoma.Transaction.generateDeltaProof witness [action] }

/-- Creates a logic for a given method. This logic is combined with other method
    and constructor logics to create the complete resource logic for an object. -/
def Method.logic
  {lab : EcosystemLabel}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method methodId)
  (args : Logic.Args lab)
  : Bool :=
    if args.isConsumed then
      match SomeType.cast args.data.memberArgs with
      | some argsData =>
        let mselfObj : Option (Object classId.label) := Object.fromResource args.self
        match mselfObj with
          | none => false
          | some selfObj =>
            method.invariant selfObj argsData
            && Logic.checkResourceData [selfObj.toSomeObject] args.consumed
            && let createdObjects := method.created selfObj argsData
               Logic.checkResourceData createdObjects args.created
      | none =>
        false
    else
      -- TODO: may need to do something more here in general, fine for the counter
      true

def Method.action
  {lab : EcosystemLabel}
  {classId : lab.ClassId}
  (methodId : classId.label.MethodId)
  (method : Class.Method methodId)
  (self : Object classId.label)
  (key : Anoma.NullifierKey)
  (args : methodId.Args.type)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let consumable : ConsumableObject classId.label :=
      { key
        object := self
        ephemeral := false }
  match consumable.consume with
  | none => pure none
  | some consumed =>
    let createObject (o : SomeObject) : CreatedObject :=
      let res : Anoma.Resource := o.toResource (ephemeral := false) (nonce := consumed.can_nullify.nullifier.toNonce)
      { object := o.object
        resource := res
        commitment := res.commitment }
    let created : List CreatedObject :=
        List.map createObject (method.created self args)
    Action.create lab classId methodId args [consumed] created

/-- Creates an Anoma Transaction for a given object method. -/
def Method.transaction
  {lab : EcosystemLabel}
  {classId : lab.ClassId}
  (methodId : classId.label.MethodId)
  (method : Class.Method methodId)
  (self : Object classId.label)
  (key : Anoma.NullifierKey)
  (args : methodId.Args.type)
  : Rand (Option Anoma.Transaction) := do
  let action ← method.action methodId self key args
  match ← method.action methodId self key args with
  | none => pure none
  | some (action, witness) =>
    pure <|
      some
        { actions := [action],
          deltaProof := Anoma.Transaction.generateDeltaProof witness [action] }

/-- Creates a logic for a given destructor. This logic is combined with other
    member logics to create the complete resource logic for an object. -/
def Destructor.logic
  {lab : EcosystemLabel}
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor destructorId)
  (args : Logic.Args lab)
  : Bool :=
    if args.isConsumed then
      match SomeType.cast args.data.memberArgs with
      | some argsData =>
        let mselfObj : Option (Object classId.label) := Object.fromResource args.self
        match mselfObj with
          | none => false
          | some selfObj =>
            Logic.checkResourceData [selfObj.toSomeObject] args.consumed
              && destructor.invariant selfObj argsData
      | none =>
        false
    else args.self.ephemeral

def Destructor.action
  {lab : EcosystemLabel}
  {classId : lab.ClassId}
  (destructorId : classId.label.DestructorId)
  (_destructor : Class.Destructor destructorId)
  (self : Object classId.label)
  (key : Anoma.NullifierKey)
  (args : destructorId.Args.type)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
  let consumable : ConsumableObject classId.label :=
       { key
         object := self
         ephemeral := false }
  match consumable.consume with
  | none => pure none
  | some consumed =>
    let createdObject : CreatedObject :=
      let ephResource := { consumed.resource with ephemeral := true }
      { object := self
        resource := ephResource
        commitment := ephResource.commitment }
    Action.create lab classId destructorId args [consumed] [createdObject]

/-- Creates an Anoma Transaction for a given object destructor. -/
def Destructor.transaction
  {lab : EcosystemLabel}
  {classId : lab.ClassId}
  (destructorId : classId.label.DestructorId)
  (destructor : Class.Destructor destructorId)
  (self : Object classId.label)
  (key : Anoma.NullifierKey)
  (args : destructorId.Args.type)
  : Rand (Option Anoma.Transaction) := do
  match ← destructor.action destructorId self key args with
  | none => pure none
  | some (action, witness) =>
    pure <|
      some
        { actions := [action],
          deltaProof := Anoma.Transaction.generateDeltaProof witness [action] }

-- Check:
-- 1. member logic corresponding to the memberId in AppData
-- 2. class invariant for the object being consumed
def checkClassMemberLogic
  {lab : EcosystemLabel}
  {classId : lab.ClassId}
  (args : Logic.Args lab)
  (eco : Ecosystem lab)
  (memberId : classId.label.MemberId)
  (margs : memberId.Args.type)
  : Bool := BoolCheck.run do
  let selfObj : Object classId.label ← BoolCheck.some (Object.fromResource args.self)
  let cls : Class classId := eco.classes classId
  BoolCheck.ret <|
    cls.invariant selfObj args &&
    match memberId with
    | .constructorId c =>
      Constructor.logic (cls.constructors c) args
    | .methodId m =>
      Method.logic (cls.methods m) args
    | .destructorId m =>
      Destructor.logic (cls.destructors m) args
