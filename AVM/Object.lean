import Anoma.Resource
import AVM.Class.Label
import Prelude.FinEnum

namespace AVM

-- how to model references?
structure Reference (lab : Class.Label) : Type where
  ref : Nat
  deriving BEq

structure SomeReference : Type where
  ref : Nat
  deriving BEq, Hashable

def Reference.forget {lab : Class.Label} (r : Reference lab) : SomeReference where
  ref := r.ref

-- unsafe
def SomeReference.coerce {lab : Class.Label} (r : SomeReference) : Reference lab where
  ref := r.ref

instance SomeReference.instTypeRep : TypeRep SomeReference where
  rep := Rep.atomic "SomeReference"

instance subObjectsBEq {lab : Class.Label} : BEq ((s : lab.SubObjectName) → Reference s.label) :=
  FinEnum.ext (fun l => Reference l.label) (enum := lab.subObjectEnum)

/-- Represents a concrete object, translated into a resource. For class
    represetation (object description), see `AVM.Class`. -/
structure Object (lab : Class.Label) : Type u where
  quantity : Nat
  /-- `privateFields` go into the `value` field of the resource -/
  privateFields : lab.PrivateFields.type
  subObjects : (s : lab.SubObjectName) → Reference s.label
  /-- The nonce should be available for objects fetched from Anoma. -/
  nonce : Option Anoma.Nonce := none
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

-- TODO consider defining a structure
def Class.Label.ValueType (clab : Class.Label) : SomeType :=
  ⟨clab.PrivateFields.type × Vector SomeReference clab.subObjectEnum.card⟩

def Object.references {clab : Class.Label} (obj : Object clab) : Vector SomeReference clab.subObjectEnum.card :=
    Vector.map (fun c => obj.subObjects c |>.forget) clab.subObjectEnum.toVector

/-- Converts SomeObject to a Resource. -/
def SomeObject.toResource
  (sobj : SomeObject)
  (ephemeral : Bool)
  (nonce : Anoma.Nonce)
  : Anoma.Resource :=
  let lab := sobj.label
  let obj : Object lab := sobj.object
  { Val := lab.ValueType,
    Label := ⟨Object.Resource.Label⟩,
    label := ⟨lab, lab.DynamicLabel.mkDynamicLabel obj.privateFields⟩,
    quantity := obj.quantity,
    value := (obj.privateFields, obj.references),
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
  let try fields : lab.ValueType.type := SomeType.cast res.value
  let privateFields := fields.1
  let enum := lab.subObjectEnum
  let subObjects : Vector SomeReference enum.card := fields.2
  some { quantity := res.quantity,
         nonce := res.nonce,
         subObjects := fun s => subObjects.get (enum.equiv s) |>.coerce
         privateFields := privateFields }

def SomeObject.fromResource
  (res : Anoma.Resource)
  : Option SomeObject :=
  let try resLab : Object.Resource.Label := tryCast res.label
  let lab : Class.Label := resLab.classLabel
  let try obj := @Object.fromResource lab res
  some {label := lab, object := obj}
