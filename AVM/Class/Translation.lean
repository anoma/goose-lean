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
import AVM.Ecosystem.Label
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
  : Message lab :=
  { id := .classMember (.constructorId constrId),
    vals,
    args,
    recipient := [newId].toVector }

def Destructor.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (_destructor : Class.Destructor classId destructorId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : destructorId.Args.type)
  : Message lab :=
  { id := .classMember (.destructorId destructorId),
    vals,
    args,
    recipient := [selfId].toVector }

def Method.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (_method : Class.Method classId methodId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  : Message lab :=
  { id := .classMember (.methodId methodId),
    vals,
    args,
    recipient := [selfId].toVector }

/-- Creates a message logic for a given constructor. -/
def Constructor.Message.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
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

/-- Creates a message logic for a given destructor. -/
def Destructor.Message.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor classId destructorId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  let try argsData := SomeType.cast msg.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! [selfRes] := consumedResObjs
  let try selfObj : Object classId.label := Object.fromResource selfRes
  Logic.checkResourcesData [selfObj.toSomeObjectData] createdResObjs
    && Logic.checkResourcesPersistent consumedResObjs
    && Logic.checkResourcesEphemeral createdResObjs
    && destructor.invariant selfObj argsData

/-- Creates a message logic for a given method. -/
def Method.Message.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  let try argsData := SomeType.cast msg.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! [selfRes] := consumedResObjs
  let try selfObj : Object classId.label := Object.fromResource selfRes
  check method.invariant selfObj argsData
  let body := method.body selfObj argsData
  let try vals : body.params.Product := tryCast msg.vals
  let createdObject : Object classId.label := body |>.returnValue vals
  Logic.checkResourcesData [createdObject.toSomeObjectData] createdResObjs
    && Logic.checkResourcesPersistent consumedResObjs
    && Logic.checkResourcesPersistent createdResObjs

/-- The class logic checks if all consumed messages in the action correspond
  to class members and the single consumed object is the receiver. -/
def logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (cl : Class classId)
  (args : Logic.Args)
  : Bool :=
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
        let try msg : Message lab := Message.fromResource res
        let! [recipient] := msg.recipient.toList
        -- NOTE: we should check that the resource logic of res corresponds to
        -- the message logic
        consumedObject.uid == recipient
