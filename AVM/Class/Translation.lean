
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
  (lab : EcosystemLabel)
  (memberId : lab.MemberId)
  (args : memberId.Args.type)
  (sconsumed : List SomeConsumedObject)
  (created : List CreatedObject) -- no appdata/logic
  : Anoma.Action :=
  let logicVerifierInputs : Std.HashMap Anoma.Tag Anoma.LogicVerifierInput :=
    Std.HashMap.emptyWithCapacity
    |>.insertMany (List.map (fun c => Prod.map id (mkLogicVerifierInput Consumed) (mkTagDataPairConsumed c)) sconsumed)
    |>.insertMany (List.map (Prod.map id (mkLogicVerifierInput Created) ∘ mkTagDataPairCreated) created)
  let createdResources := List.map CreatedObject.resource created
  let consumedUnits : List Anoma.ComplianceUnit :=
    List.map (fun ⟨c⟩ => Anoma.ComplianceUnit.create
      { consumedResource := c.resource
        createdResource := dummyResource
        nfKey := c.key }) sconsumed
  let createdUnits : List Anoma.ComplianceUnit :=
    List.map (fun res => Anoma.ComplianceUnit.create
      { consumedResource := dummyResource
        createdResource := res
        nfKey := Anoma.NullifierKey.universal }) createdResources
  { complianceUnits := consumedUnits ++ createdUnits,
    logicVerifierInputs }
  where
    mkLogicVerifierInput (status : ConsumedCreated) (data : SomeAppData) : Anoma.LogicVerifierInput :=
      { Data := ⟨SomeAppData⟩,
        status,
        appData := data }

    mkTagDataPairConsumed : SomeConsumedObject → Anoma.Tag × SomeAppData := fun ⟨i⟩ =>
      (Anoma.Tag.Consumed i.nullifierProof.nullifier,
        { appData := {
            memberId := memberId,
            memberArgs := args }})

    mkTagDataPairCreated (i : CreatedObject)
     : Anoma.Tag × SomeAppData :=
      (Anoma.Tag.Created i.commitment,
        {label := lab,
         appData := {
          memberId := .falseLogicId,
          memberArgs := UUnit.unit }})

end AVM.Ecosystem

namespace AVM.Class

open Ecosystem

private def Action.create
  (lab : EcosystemLabel)
  (classId : lab.ClassId)
  (memberId : classId.MemberId)
  (args : memberId.Args.type)
  (sconsumed : List SomeConsumedObject)
  (created : List CreatedObject) -- no appdata/logic
  : Anoma.Action :=
  let logicVerifierInputs : Std.HashMap Anoma.Tag Anoma.LogicVerifierInput :=
    Std.HashMap.emptyWithCapacity
    |>.insertMany (List.map (fun c => Prod.map id (mkLogicVerifierInput Consumed) (mkTagDataPairConsumed c)) sconsumed)
    |>.insertMany (List.map (Prod.map id (mkLogicVerifierInput Created) ∘ mkTagDataPairCreated) created)
  let createdResources := List.map CreatedObject.resource created
  let consumedUnits : List Anoma.ComplianceUnit :=
    List.map (fun ⟨c⟩ => Anoma.ComplianceUnit.create
      { consumedResource := c.resource
        createdResource := dummyResource
        nfKey := c.key }) sconsumed
  let createdUnits : List Anoma.ComplianceUnit :=
    List.map (fun res => Anoma.ComplianceUnit.create
      { consumedResource := dummyResource
        createdResource := res
        nfKey := Anoma.NullifierKey.universal }) createdResources
  { complianceUnits := consumedUnits ++ createdUnits,
    logicVerifierInputs }
  where
    mkLogicVerifierInput (status : ConsumedCreated) (data : SomeAppData) : Anoma.LogicVerifierInput :=
      { Data := ⟨SomeAppData⟩,
        status,
        appData := data }

    mkTagDataPairConsumed : SomeConsumedObject → Anoma.Tag × SomeAppData := fun ⟨i⟩ =>
      (Anoma.Tag.Consumed i.nullifierProof.nullifier,
        { appData := {
            memberId := .classMember memberId,
            memberArgs := args }})

    mkTagDataPairCreated (i : CreatedObject)
     : Anoma.Tag × SomeAppData :=
      (Anoma.Tag.Created i.commitment,
        {label := lab,
         appData := {
          memberId := .falseLogicId,
          memberArgs := UUnit.unit }})

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
  : Anoma.Action :=
    -- TODO: set nonce properly
    let clab := classId.label
    let newObj : Object clab := constr.created args
    let consumable : ConsumableObject clab :=
       { object := {newObj with nullifierKeyCommitment := Anoma.NullifierKeyCommitment.universal}
         ephemeral := true
         key := Anoma.NullifierKey.universal }
    let consumed : ConsumedObject clab := { consumable with nullifierProof := Anoma.nullifyUniversal consumable.resource consumable.key rfl rfl }
    let created : List CreatedObject :=
          [CreatedObject.fromSomeObject (newObj.toSomeObject) (ephemeral := false)]
    Action.create lab classId constrId args [consumed] created

/-- Creates an Anoma Transaction for a given object construtor. -/
def Constructor.transaction
  {lab : EcosystemLabel}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor constrId)
  (args : constrId.Args.type)
  : Anoma.Transaction :=
    let action := constr.action args
    { actions := [action],
      -- TODO: automatically generate deltaProof that verifies that the transaction is balanced
      deltaProof := "" }

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
  : Option Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let consumable : ConsumableObject classId.label :=
      { key
        object := self
        ephemeral := false }
  match consumable.consume with
  | none => none
  | some consumed =>
    let createObject (o : SomeObject) : CreatedObject :=
      let res : Anoma.Resource := o.toResource false
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
  : Option Anoma.Transaction := do
  let action ← method.action methodId self key args
  pure { actions := [action],
         -- TODO: set deltaProof properly
         deltaProof := "" }

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
  : Option Anoma.Action :=
  let consumable : ConsumableObject classId.label :=
       { key
         object := self
         ephemeral := false }
  match consumable.consume with
  | none => none
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
  : Option Anoma.Transaction := do
  let action ← destructor.action destructorId self key args
  pure { actions := [action],
         -- TODO: set deltaProof properly
         deltaProof := "" }

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
