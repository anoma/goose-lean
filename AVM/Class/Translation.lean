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

mutual

partial def Member.Call.task {lab : Ecosystem.Label} (eco : Ecosystem lab) (call : Member.Call lab) : Task :=
  match call with
  | .constructor classId constrId newId args =>
    eco.classes classId |>.constructors constrId |>.task eco newId args
  | .destructor classId destrId selfId args =>
    eco.classes classId |>.destructors destrId |>.task eco selfId args
  | .method classId methodId selfId args =>
    eco.classes classId |>.methods methodId |>.task eco selfId args

/-- Creates a Task for a given object constructor. -/
partial def Constructor.task
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  (newId : ObjectId)
  (args : constrId.Args.type)
  : Task :=
  let result := constr.body args
  let calls : List (Member.Call lab) := result.calls
  let tasks := calls.map (·.task eco)
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
  Task.compose tasks (constr.message newObj.uid args) consumedObject [createdObject]

/-- Creates an Anoma Transaction for a given object destructor. -/
partial def Destructor.task
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor classId destructorId)
  (selfId : ObjectId)
  (args : destructorId.Args.type)
  : Task :=
  let consumedObjectId : TypedObjectId := ⟨classId.label, selfId⟩
  let createdObjects (self : Object classId.label) : List CreatedObject :=
    [{ uid := self.uid,
       data := self.data,
       ephemeral := true }]
  let tasks (self : Object classId.label) : List Task :=
    (destructor.body self args).calls.map (·.task eco)
  Task.composeWithFetch (destructor.message selfId args) consumedObjectId tasks createdObjects

partial def Method.task
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  : Task :=
  let consumedObjectId : TypedObjectId := ⟨classId.label, selfId⟩
  let createdObjects (self : Object classId.label) : List CreatedObject :=
    let obj := (method.body self args).returnValue.toSomeObject
    [{ uid := obj.object.uid,
       data := obj.object.data,
       ephemeral := false }]
  let tasks (self : Object classId.label) : List Task :=
    (method.body self args).calls.map (·.task eco)
  Task.composeWithFetch (method.message selfId args) consumedObjectId tasks createdObjects

end -- mutual
