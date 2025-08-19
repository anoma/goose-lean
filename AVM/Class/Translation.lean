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
import AVM.Task

namespace AVM.Class

/-- Creates a message logic for a given constructor. -/
def Constructor.Message.logic
  {lab : Class.Label}
  {constrId : lab.ConstructorId}
  (constr : Class.Constructor constrId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  let try argsData := SomeType.cast msg.args
  let newObjData := constr.created argsData
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  Logic.checkResourcesData [newObjData.toSomeObjectData] consumedResObjs
    && Logic.checkResourcesData [newObjData.toSomeObjectData] createdResObjs
    && Logic.checkResourcesEphemeral consumedResObjs
    && Logic.checkResourcesPersistent createdResObjs
    && constr.invariant argsData

def Constructor.message
  {lab : Class.Label}
  {constrId : lab.ConstructorId}
  (_constr : Class.Constructor constrId)
  (newId : ObjectId)
  (args : constrId.Args.type)
  : Message lab :=
  { id := Label.MemberId.constructorId constrId,
    args,
    recipient := newId }

/-- Creates an action for a given constructor. This action creates the
  object specified by the constructor. -/
def Constructor.action'
  (g : StdGen)
  {lab : Class.Label}
  {constrId : lab.ConstructorId}
  (constr : Class.Constructor constrId)
  (newId : ObjectId)
  (args : constrId.Args.type)
  : Anoma.Action × Anoma.DeltaWitness × StdGen :=
  let newObjData : ObjectData lab := constr.created args
  let newObj : Object lab :=
    { uid := newId,
      nonce := ⟨newId⟩,
      data := newObjData }
  let consumable : ConsumableObject lab :=
      { object := newObj
        ephemeral := true }
  let consumedObject : ConsumedObject lab :=
    { consumable with can_nullify := consumable.toResource.nullifyUniversal }
  let createdObject : CreatedObject :=
    CreatedObject.fromSomeObject newObj.toSomeObject (ephemeral := false)
  let consumedMessage : Message lab :=
    constr.message newObj.uid args
  Action.create' g [consumedObject] [createdObject] [consumedMessage] []

def Constructor.task'
  (g : StdGen)
  {lab : Class.Label}
  {constrId : lab.ConstructorId}
  (constr : Class.Constructor constrId)
  (args : constrId.Args.type)
  : Task × StdGen :=
  let (newId, g') := stdNext g
  let (action, witness, g'') := constr.action' g' newId args
  let task : Task :=
    { params := [],
      message := constr.message newId args,
      actions := fun _ => pure <| some ⟨[action], witness⟩ }
  (task, g'')

/-- Creates a Task for a given object constructor. -/
def Constructor.task
  {lab : Class.Label}
  {constrId : lab.ConstructorId}
  (constr : Class.Constructor constrId)
  (args : constrId.Args.type)
  : Rand Task := do
  let g ← get
  let (task, g') := constr.task' g.down args
  set (ULift.up g')
  return task

/-- Creates a logic for a given method. -/
def Method.Message.logic
  {lab : Class.Label}
  {methodId : lab.MethodId}
  (method : Class.Method methodId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  let try argsData := SomeType.cast msg.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! [selfRes] := consumedResObjs
  let try selfObj : Object lab := Object.fromResource selfRes
  check method.invariant selfObj argsData
  let createdObjects := method.created selfObj argsData
  Logic.checkResourcesData (List.map SomeObject.toSomeObjectData createdObjects) createdResObjs
    && Logic.checkResourcesPersistent consumedResObjs
    && Logic.checkResourcesPersistent createdResObjs

def Method.message
  {lab : Class.Label}
  {methodId : lab.MethodId}
  (_method : Class.Method methodId)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  : Message lab :=
  { id := Label.MemberId.methodId methodId,
    args,
    recipient := selfId }

def Method.action
  {lab : Class.Label}
  (methodId : lab.MethodId)
  (method : Class.Method methodId)
  (self : Object lab)
  (args : methodId.Args.type)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
  let consumable : ConsumableObject lab :=
      { object := self
        ephemeral := false }
  let try consumedObject : ConsumedObject lab := consumable.consume
  let createObject (o : SomeObject) : CreatedObject :=
    { uid := o.object.uid,
      data := o.object.data,
      ephemeral := false }
  let createdObjects : List CreatedObject :=
    List.map createObject (method.created self args)
  let consumedMessage : Message lab :=
    method.message self.uid args
  Action.create [consumedObject] createdObjects [consumedMessage] []

def Method.task
  {lab : Class.Label}
  (methodId : lab.MethodId)
  (method : Class.Method methodId)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  : Task :=
  { params := [⟨lab, selfId⟩],
    message := method.message selfId args,
    actions := fun (self, _) => do
      let try (action, witness) ← method.action methodId self args
      pure <| some { actions := [action], deltaWitness := witness } }

/-- Creates a logic for a given destructor. This logic is combined with other
    member logics to create the complete resource logic for an object. -/
def Destructor.Message.logic
  {lab : Class.Label}
  {destructorId : lab.DestructorId}
  (destructor : Class.Destructor destructorId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  let try argsData := SomeType.cast msg.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! [selfRes] := consumedResObjs
  let try selfObj : Object lab := Object.fromResource selfRes
  Logic.checkResourcesData [selfObj.toSomeObjectData] createdResObjs
    && Logic.checkResourcesPersistent consumedResObjs
    && Logic.checkResourcesEphemeral createdResObjs
    && destructor.invariant selfObj argsData

def Destructor.message
  {lab : Class.Label}
  {destructorId : lab.DestructorId}
  (_destructor : Class.Destructor destructorId)
  (selfId : ObjectId)
  (args : destructorId.Args.type)
  : Message lab :=
  { id := Label.MemberId.destructorId destructorId,
    args,
    recipient := selfId }

def Destructor.action
  {lab : Class.Label}
  (destructorId : lab.DestructorId)
  (destructor : Class.Destructor destructorId)
  (self : Object lab)
  (args : destructorId.Args.type)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
  let consumable : ConsumableObject lab :=
       { object := self
         ephemeral := false }
  let try consumedObject := consumable.consume
  let createdObject : CreatedObject :=
    { uid := self.uid,
      data := self.data,
      ephemeral := true }
  let consumedMessage : Message lab := destructor.message self.uid args
  Action.create [consumedObject] [createdObject] [consumedMessage] []

/-- Creates an Anoma Transaction for a given object destructor. -/
def Destructor.task
  {lab : Class.Label}
  (destructorId : lab.DestructorId)
  (destructor : Class.Destructor destructorId)
  (selfId : ObjectId)
  (args : destructorId.Args.type)
  : Task :=
  { params := [⟨lab, selfId⟩],
    message := destructor.message selfId args,
    actions := fun (self, _) => do
      let try (action, witness) ← destructor.action destructorId self args
      pure <| some { actions := [action], deltaWitness := witness } }

/-- The class logic checks if all consumed messages in the action correspond
  to class members and the single consumed object is the receiver. -/
def logic {lab : Class.Label} (args : Logic.Args) : Bool :=
  match args.status with
  | Created => true
  | Consumed =>
    let consumedMessageResources : List Anoma.Resource := Logic.selectMessageResources args.consumed
    let! [consumedObjectResource] : List Anoma.Resource := Logic.selectObjectResources args.consumed
    let try consumedObject : Object lab := Object.fromResource consumedObjectResource
    consumedMessageResources.length + 1 == (Logic.filterOutDummy args.consumed).length
      && consumedMessageResources.all fun res =>
        let try msg : Message lab := Message.fromResource res
        consumedObject.uid == msg.recipient
