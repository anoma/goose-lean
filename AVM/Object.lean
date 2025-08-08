
import Anoma.Resource
import AVM.Class.Label

namespace AVM

structure Object.Data (lab : Class.Label) where
  /-- Object quantity, stored in the `quantity` field of the resource. -/
  quantity : Nat
  /-- `privateFields` go into the `value` field of the resource. -/
  privateFields : lab.PrivateFields.type
  deriving BEq

/-- Represents a concrete object, translated into a resource. For class
    represetation (object description), see `AVM.Class`. -/
structure Object (lab : Class.Label) : Type u where
  /-- Unique object identifier. Stored in the `value` field of the resource. -/
  uid : Anoma.ObjectId
  nonce : Anoma.Nonce
  data : Object.Data lab
  deriving BEq

instance Object.hasTypeRep (lab : Class.Label) : TypeRep (Object lab) where
  rep := Rep.composite "AVM.Object" [Rep.atomic lab.name]

structure SomeObject where
  {label : Class.Label}
  object : Object label

instance SomeObject.hasTypeRep : TypeRep SomeObject where
  rep := Rep.atomic "AVM.SomeObject"

instance SomeObject.hasBEq : BEq SomeObject where
  beq a b := a.label === b.label && a.object === b.object

def Object.toSomeObject {lab : Class.Label} (object : Object lab) : SomeObject := {object}

structure Object.Resource.Label where
  /-- The label of the class -/
  classLabel : Class.Label
  /-- The dynamic label is used to put dynamic data into the Resource label -/
  dynamicLabel : classLabel.DynamicLabel.Label.type

instance : TypeRep Object.Resource.Label where
  rep := Rep.atomic "Object.Resource.Label"

instance : BEq Object.Resource.Label where
  beq o1 o2 := o1.classLabel == o2.classLabel && o1.dynamicLabel === o2.dynamicLabel

structure Object.Resource.Value (lab : Class.Label) where
  uid : Anoma.ObjectId
  privateFields : lab.PrivateFields.type

instance {lab : Class.Label} : TypeRep (Object.Resource.Value lab) where
  rep := Rep.composite "Object.Resource.Value" [Rep.atomic lab.name]

instance {lab : Class.Label} : BEq (Object.Resource.Value lab) where
  beq v1 v2 := v1.uid == v2.uid && v1.privateFields === v2.privateFields

/-- Converts SomeObject to a Resource. -/
def SomeObject.toResource
  (sobj : SomeObject)
  (ephemeral : Bool)
  (nonce : Anoma.Nonce)
  : Anoma.Resource :=
  let lab := sobj.label
  let obj : Object lab := sobj.object
  { Val := ⟨Object.Resource.Value lab⟩,
    Label := ⟨Object.Resource.Label⟩,
    label := ⟨lab, lab.DynamicLabel.mkDynamicLabel obj.data.privateFields⟩,
    quantity := obj.data.quantity,
    value := ⟨obj.uid, obj.data.privateFields⟩,
    ephemeral := ephemeral,
    nonce,
    nullifierKeyCommitment := default }

/-- Converts Object to a Resource. -/
def Object.toResource {lab : Class.Label} (obj : Object lab) (ephemeral : Bool) (nonce : Anoma.Nonce) : Anoma.Resource
 := obj.toSomeObject.toResource ephemeral nonce

def Object.fromResource
  {lab : Class.Label}
  (res : Anoma.Resource)
  : Option (Object lab) :=
  let try resLab : Object.Resource.Label := tryCast res.label
  check (resLab.classLabel == lab)
  let try value : Object.Resource.Value lab := tryCast res.value
  some {  uid := value.uid,
          data := ⟨res.quantity, value.privateFields⟩,
          nonce := res.nonce }

def SomeObject.fromResource
  (res : Anoma.Resource)
  : Option SomeObject :=
  let try resLab : Object.Resource.Label := tryCast res.label
  let lab : Class.Label := resLab.classLabel
  let try obj := @Object.fromResource lab res
  some {label := lab, object := obj}
