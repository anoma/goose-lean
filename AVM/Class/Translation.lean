import Mathlib.Control.Random
import Prelude
import Anoma
import AVM.Class
import AVM.Action
import AVM.Class.Label
import AVM.Object
import AVM.Object.Consumed
import AVM.Class.Member
import AVM.Logic
import AVM.Message
import AVM.Ecosystem
import AVM.Task

namespace AVM.Class

def Constructor.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (_constr : Class.Constructor classId constrId)
  (newId : ObjectId)
  (args : constrId.Args.type)
  : Message classId.label :=
  { id := Label.MemberId.constructorId constrId,
    args,
    recipient := newId }

def Destructor.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (_destructor : Class.Destructor classId destructorId)
  (selfId : ObjectId)
  (args : destructorId.Args.type)
  : Message classId.label :=
  { id := Label.MemberId.destructorId destructorId,
    args,
    recipient := selfId }

def Method.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (_method : Class.Method classId methodId)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  : Message classId.label :=
  { id := Label.MemberId.methodId methodId,
    args,
    recipient := selfId }

/-- Creates a message logic for a given constructor. -/
def Constructor.Message.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message classId.label := Message.fromResource args.self
  let try argsData := SomeType.cast msg.args
  let newObjData := constr.body argsData |>.returnValue
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  Logic.checkResourcesData [newObjData.toSomeObjectData] consumedResObjs
    && Logic.checkResourcesData [newObjData.toSomeObjectData] createdResObjs
    && Logic.checkResourcesEphemeral consumedResObjs
    && Logic.checkResourcesPersistent createdResObjs
    && constr.invariant argsData

/-- Creates a logic for a given destructor. This logic is combined with other
    member logics to create the complete resource logic for an object. -/
def Destructor.Message.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor classId destructorId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message classId.label := Message.fromResource args.self
  let try argsData := SomeType.cast msg.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! [selfRes] := consumedResObjs
  let try selfObj : Object classId.label := Object.fromResource selfRes
  Logic.checkResourcesData [selfObj.toSomeObjectData] createdResObjs
    && Logic.checkResourcesPersistent consumedResObjs
    && Logic.checkResourcesEphemeral createdResObjs
    && destructor.invariant selfObj argsData

/-- Creates a logic for a given method. -/
def Method.Message.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message classId.label := Message.fromResource args.self
  let try argsData := SomeType.cast msg.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! [selfRes] := consumedResObjs
  let try selfObj : Object classId.label := Object.fromResource selfRes
  check method.invariant selfObj argsData
  let createdObject : Object classId.label := method.body selfObj argsData |>.returnValue
  Logic.checkResourcesData [createdObject.toSomeObjectData] createdResObjs
    && Logic.checkResourcesPersistent consumedResObjs
    && Logic.checkResourcesPersistent createdResObjs

/-- The class logic checks if all consumed messages in the action correspond
  to class members and the single consumed object is the receiver. -/
def logic {lab : Ecosystem.Label} {classId : lab.ClassId} (cl : Class classId) (args : Logic.Args) : Bool :=
  let try self : Object classId.label := Object.fromResource args.self
  check cl.invariant self args
  match args.status with
  | Created => true
  | Consumed =>
    let consumedMessageResources : List Anoma.Resource := Logic.selectMessageResources args.consumed
    let! [consumedObjectResource] : List Anoma.Resource := Logic.selectObjectResources args.consumed
    let try consumedObject : Object classId.label := Object.fromResource consumedObjectResource
    consumedMessageResources.length + 1 == (Logic.filterOutDummy args.consumed).length
      && consumedMessageResources.all fun res =>
        let try msg : Message classId.label := Message.fromResource res
        -- NOTE: we should check that the resource logic of res corresponds to
        -- the message logic
        consumedObject.uid == msg.recipient

def Member.Call.task {lab : Ecosystem.Label} (call : Member.Call lab) : Task :=
  match call with
  | .constructor lab constrId newId =>
    sorry
  | .destructor lab destrId selfId =>
    sorry
  | .method lab methodId selfId =>
    sorry

/-- Creates an action for a given constructor. This action creates the
  object specified by the constructor. -/
def Constructor.action
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  (newId : ObjectId)
  (args : constrId.Args.type)
  : Rand (Anoma.Action × Anoma.DeltaWitness) :=
  let result := constr.body args
  let newObjData : ObjectData classId.label := result.returnValue
  let newObj : Object classId.label :=
    { uid := newId,
      nonce := ⟨newId⟩,
      data := newObjData }
  let consumable : ConsumableObject classId.label :=
      { object := newObj
        ephemeral := true }
  let consumedObject : ConsumedObject classId.label :=
    { consumable with can_nullify := consumable.toResource.nullifyUniversal }
  let createdObject : CreatedObject :=
    CreatedObject.fromSomeObject newObj.toSomeObject (ephemeral := false)
  let consumedMessage : Message classId.label :=
    constr.message newObj.uid args
  Action.create [consumedObject] [createdObject] [consumedMessage] []

/-- Creates a Task for a given object constructor. -/
def Constructor.task
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  (newId : ObjectId)
  (args : constrId.Args.type)
  : Task :=
  { params := [],
    message := constr.message newId args,
    actions := fun _ => do
      let (action, witness) ← constr.action newId args
      pure <| some ⟨[action], witness⟩ }

def Method.action
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (methodId : classId.label.MethodId)
  (method : Class.Method classId methodId)
  (self : Object classId.label)
  (args : methodId.Args.type)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
  let result := method.body self args
  let consumable : ConsumableObject classId.label :=
      { object := self
        ephemeral := false }
  let try consumedObject : ConsumedObject classId.label := consumable.consume
  let createObject (o : SomeObject) : CreatedObject :=
    { uid := o.object.uid,
      data := o.object.data,
      ephemeral := false }
  let createdObject : CreatedObject := createObject result.returnValue.toSomeObject
  let consumedMessage : Message classId.label :=
    method.message self.uid args
  Action.create [consumedObject] [createdObject] [consumedMessage] []

def Method.task
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (methodId : classId.label.MethodId)
  (method : Class.Method classId methodId)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  : Task :=
  { params := [⟨classId.label, selfId⟩],
    message := method.message selfId args,
    actions := fun (self, _) => do
      let try (action, witness) ← method.action methodId self args
      pure <| some { actions := [action], deltaWitness := witness } }

def Destructor.action
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (destructorId : classId.label.DestructorId)
  (destructor : Class.Destructor classId destructorId)
  (self : Object classId.label)
  (args : destructorId.Args.type)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
  let consumable : ConsumableObject classId.label :=
       { object := self
         ephemeral := false }
  let try consumedObject := consumable.consume
  let createdObject : CreatedObject :=
    { uid := self.uid,
      data := self.data,
      ephemeral := true }
  let consumedMessage : Message classId.label := destructor.message self.uid args
  Action.create [consumedObject] [createdObject] [consumedMessage] []

/-- Creates an Anoma Transaction for a given object destructor. -/
def Destructor.task
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (destructorId : classId.label.DestructorId)
  (destructor : Class.Destructor classId destructorId)
  (selfId : ObjectId)
  (args : destructorId.Args.type)
  : Task :=
  { params := [⟨classId.label, selfId⟩],
    message := destructor.message selfId args,
    actions := fun (self, _) => do
      let try (action, witness) ← destructor.action destructorId self args
      pure <| some { actions := [action], deltaWitness := witness } }
