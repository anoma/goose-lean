import Anoma.Resource
import AVM.Ecosystem.Label.Base

namespace AVM

structure ObjectData {lab : Ecosystem.Label} (c : lab.ClassId) where
  /-- Object quantity, stored in the `quantity` field of the resource. -/
  quantity : Nat
  /-- `privateFields` go into the `value` field of the resource. -/
  privateFields : c.label.PrivateFields.type
  deriving BEq

instance ObjectData.inhabited {lab : Ecosystem.Label} (c : lab.ClassId) : Inhabited (ObjectData c) where
  default := {quantity := 0, privateFields := c.label.privateFieldsInhabited.default}

instance ObjectData.hasTypeRep {lab : Ecosystem.Label} (c : lab.ClassId) : TypeRep (ObjectData c) where
  rep := Rep.composite "AVM.ObjectData" [Rep.atomic lab.name, Rep.atomic c.label.name]

structure SomeObjectData : Type 1 where
  {label : Ecosystem.Label}
  {classId : label.ClassId}
  data : ObjectData classId

instance SomeObjectData.hasTypeRep : TypeRep SomeObjectData where
  rep := Rep.atomic "AVM.SomeObjectData"

instance SomeObjectData.hasBEq : BEq SomeObjectData where
  beq a b := a.label === b.label && a.data === b.data

structure ObjectValue : Type 1 where
  {label : Ecosystem.Label}
  {classId : label.ClassId}
  uid : ObjectId
  data : ObjectData classId

instance ObjectValue.hasTypeRep : TypeRep ObjectValue where
  rep := Rep.atomic "AVM.ObjectValue"

instance ObjectValue.hasBEq : BEq ObjectValue where
  beq a b := a.label === b.label
          && a.uid == b.uid
          && a.data === b.data

def ObjectData.toSomeObjectData {lab : Ecosystem.Label} {c : lab.ClassId} (data : ObjectData c) : SomeObjectData :=
  ⟨data⟩

def ObjectData.toObjectValue {lab : Ecosystem.Label} {c : lab.ClassId} (uid : ObjectId) (data : ObjectData c) : ObjectValue :=
  ⟨uid, data⟩

/-- Represents a concrete object, translated into a resource. For class
    represetation (object description), see `AVM.Class`. -/
structure Object {lab : Ecosystem.Label} (c : lab.ClassId) : Type where
  /-- Unique object identifier. Stored in the `value` field of the resource. -/
  uid : Anoma.ObjectId
  nonce : Anoma.Nonce
  data : ObjectData c
  deriving BEq, Inhabited

instance Object.hasTypeRep {lab : Ecosystem.Label} (c : lab.ClassId) : TypeRep (Object c) where
  rep := Rep.composite "AVM.Object" [Rep.atomic lab.name, Rep.atomic c.label.name]

structure SomeObject where
  {label : Ecosystem.Label}
  {classId : label.ClassId}
  object : Object classId

instance SomeObject.hasTypeRep : TypeRep SomeObject where
  rep := Rep.atomic "AVM.SomeObject"

instance SomeObject.hasBEq : BEq SomeObject where
  beq a b := a.label === b.label && a.object === b.object

def Object.toSomeObject {lab : Ecosystem.Label} {c : lab.ClassId} (object : Object c) : SomeObject := ⟨object⟩

def Object.toObjectValue {lab : Ecosystem.Label} {c : lab.ClassId} (obj : Object c) : ObjectValue :=
  obj.data.toObjectValue obj.uid

def SomeObject.toObjectValue (object : SomeObject) : ObjectValue where
  data := object.object.data
  uid := object.object.uid

structure Object.Resource.Label where
  /-- The label of the ecosystem -/
  label : Ecosystem.Label
  /-- The id of the class -/
  classId : label.ClassId
  /-- The dynamic label is used to put dynamic data into the Resource label -/
  dynamicLabel : classId.label.DynamicLabel.Label.type

instance : TypeRep Object.Resource.Label where
  rep := Rep.atomic "Object.Resource.Label"

instance : BEq Object.Resource.Label where
  beq o1 o2 :=
    o1.label == o2.label
    && o1.classId.label == o2.classId.label
    && o1.dynamicLabel === o2.dynamicLabel

structure Object.Resource.Value {lab : Ecosystem.Label} (classId : lab.ClassId) where
  uid : Anoma.ObjectId
  privateFields : classId.label.PrivateFields.type

instance {lab : Ecosystem.Label} {classId : lab.ClassId} : TypeRep (Object.Resource.Value classId) where
  rep := Rep.composite "Object.Resource.Value" [Rep.atomic lab.name, Rep.atomic classId.label.name]

instance {lab : Ecosystem.Label} {classId : lab.ClassId} : BEq (Object.Resource.Value classId) where
  beq v1 v2 := v1.uid == v2.uid && v1.privateFields === v2.privateFields

/-- Converts SomeObject to a Resource. -/
def SomeObject.toResource
  (sobj : SomeObject)
  (ephemeral : Bool)
  : Anoma.Resource :=
  let classId := sobj.classId
  let clab := classId.label
  let label := sobj.label
  let obj : Object classId := sobj.object
  { Label := ⟨Object.Resource.Label⟩,
    label := { label
               classId
               dynamicLabel := clab.DynamicLabel.mkDynamicLabel obj.data.privateFields }
    logicRef := label.logicRef,
    quantity := obj.data.quantity,
    Val := ⟨Object.Resource.Value classId⟩,
    value := ⟨obj.uid, obj.data.privateFields⟩,
    ephemeral := ephemeral,
    nonce := obj.nonce,
    nullifierKeyCommitment := default }

/-- Converts Object to a Resource. -/
def Object.toResource {lab : Ecosystem.Label} {c : lab.ClassId} (obj : Object c) (ephemeral : Bool) : Anoma.Resource
 := obj.toSomeObject.toResource ephemeral

def Object.fromResource
  {lab : Ecosystem.Label}
  {c : lab.ClassId}
  (res : Anoma.Resource)
  : Option (Object c) :=
  let try resLab : Object.Resource.Label := tryCast res.label
  check (resLab.label == lab)
  check (res.logicRef == lab.logicRef)
  let try value : Object.Resource.Value c := tryCast res.value
  some {  uid := value.uid,
          data := ⟨res.quantity, value.privateFields⟩,
          nonce := res.nonce }

def SomeObject.fromResource.{u, v}
  (res : Anoma.Resource.{u, v})
  : Option SomeObject.{max u v + 1} :=
  let try resLab : Object.Resource.Label := tryCast res.label
  let label : Ecosystem.Label := resLab.label
  let classId := resLab.classId
  let try object := @Object.fromResource label classId res
  some { label
         classId
         object }

def Resource.isSomeObject.{u, v} (res : Anoma.Resource.{u, v}) : Bool :=
  Option.isSome (SomeObject.fromResource.{u, v} res)
