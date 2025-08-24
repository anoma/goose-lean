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
  (Vals : SomeType)
  (vals : Vals.type)
  (newId : ObjectId)
  (args : constrId.Args.type)
  : Message classId.label :=
  { id := Label.MemberId.constructorId constrId,
    vals,
    args,
    recipient := newId }

def Destructor.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (_destructor : Class.Destructor classId destructorId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : destructorId.Args.type)
  : Message classId.label :=
  { id := Label.MemberId.destructorId destructorId,
    vals,
    args,
    recipient := selfId }

def Method.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (_method : Class.Method classId methodId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  : Message classId.label :=
  { id := Label.MemberId.methodId methodId,
    vals,
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
  let try vals : (constr.body argsData).params.Product := tryCast msg.vals
  let newObjData := constr.body argsData |>.returnValue vals
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
  let try vals : (method.body selfObj argsData).params.Product := tryCast msg.vals
  let createdObject : Object classId.label := method.body selfObj argsData |>.returnValue vals
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

partial def Member.Body.tasks {α} {params : Task.Parameters} {lab : Ecosystem.Label} (eco : Ecosystem lab) (body : Member.Body lab α params) (vals : body.params.Product) : List Task :=
  let vals1 := Member.Body.prefixProduct body vals
  match body with
  | .constructor classId constrId args next =>
    let constr := eco.classes classId |>.constructors constrId
    let task := constr.task eco (args vals1)
    task :: next.tasks eco vals
  | .destructor classId destrId selfId args next =>
    let destr := eco.classes classId |>.destructors destrId
    let task := destr.task eco (selfId vals1) (args vals1)
    task :: next.tasks eco vals
  | .method classId methodId selfId args next =>
    let destr := eco.classes classId |>.methods methodId
    let task := destr.task eco (selfId vals1) (args vals1)
    task :: next.tasks eco vals
  | .fetch _ next =>
    next.tasks eco vals
  | .return _ =>
    []

/-- Creates a Task for a given object constructor. -/
partial def Constructor.task
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  (args : constrId.Args.type)
  : Task :=
  let bodyParams := (constr.body args).params
  let params := Task.Parameters.genId (fun _ => bodyParams)
  Task.absorbParams params fun ⟨newId, vals⟩ =>
    let body := constr.body args
    let tasks := body.tasks eco vals
    let newObjData : ObjectData classId.label := body.returnValue vals
    let newObj : SomeObject :=
      let obj : Object classId.label :=
        { uid := newId,
          nonce := ⟨newId⟩,
          data := newObjData }
      obj.toSomeObject
    let consumedObj := newObj.toConsumable (ephemeral := true)
    let createdObjects : List CreatedObject :=
      [CreatedObject.fromSomeObject newObj (ephemeral := false)]
    Task.compose (constr.message ⟨bodyParams.Product⟩ vals newId args) tasks consumedObj createdObjects

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
  let bodyParams (self : Object classId.label) := (destructor.body self args).params
  let params := Task.Parameters.fetch consumedObjectId bodyParams
  Task.absorbParams params fun ⟨self, vals⟩ =>
    let tasks : List Task := (destructor.body self args).tasks eco vals
    let consumedObj := self.toSomeObject.toConsumable (ephemeral := false)
    let createdObjects : List CreatedObject :=
      [{ uid := self.uid,
         data := self.data,
         ephemeral := true }]
    Task.compose (destructor.message ⟨(bodyParams self).Product⟩ vals selfId args) tasks consumedObj createdObjects

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
  let bodyParams (self : Object classId.label) := (method.body self args).params
  let params := Task.Parameters.fetch consumedObjectId bodyParams
  Task.absorbParams params fun ⟨self, vals⟩ =>
    let body := method.body self args
    let tasks : List Task := body.tasks eco vals
    let consumedObj := self.toSomeObject.toConsumable (ephemeral := false)
    let obj := (body.returnValue vals).toSomeObject
    let createdObjects : List CreatedObject :=
      [{ uid := obj.object.uid,
         data := obj.object.data,
         ephemeral := false }]
    Task.compose (method.message ⟨(bodyParams self).Product⟩ vals selfId args) tasks consumedObj createdObjects

end -- mutual
