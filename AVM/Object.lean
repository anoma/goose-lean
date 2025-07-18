
import Anoma.Resource
import AVM.Class.Label

namespace AVM

/-- Represents a concrete object, translated into a resource. For class
    represetation (object description), see `AVM.Class`. -/
structure Object (lab : Class.Label) : Type u where
  /-- The nonce should be available for objects fetched from Anoma. -/
  nonce : Option Anoma.Nonce := none
  /-- Used to prove ownership -/
  nullifierKeyCommitment : Option Anoma.NullifierKeyCommitment
  quantity : Nat
  /-- `privateFields` go into the `value` field of the resource -/
  privateFields : lab.PrivateFields.type
  deriving BEq

instance Object.hasTypeRep (lab : Class.Label) : TypeRep (Object lab) where
  rep := Rep.composite "AVM.Object" [Rep.atomic lab.name]

def Object.nullifierKeyCommitment! {lab : Class.Label} (o : Object lab) : Anoma.NullifierKeyCommitment :=
  o.nullifierKeyCommitment.getD Anoma.NullifierKeyCommitment.universal

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

/-- Converts SomeObject to a Resource. -/
def SomeObject.toResource
  (sobj : SomeObject)
  (ephemeral : Bool)
  (nonce : Anoma.Nonce)
  : Anoma.Resource :=
  let lab := sobj.label
  let obj : Object lab := sobj.object
  { Val := lab.PrivateFields,
    Label := ⟨Object.Resource.Label⟩,
    label := ⟨lab, lab.DynamicLabel.mkDynamicLabel obj.privateFields⟩,
    quantity := obj.quantity,
    value := obj.privateFields,
    ephemeral := ephemeral,
    nonce,
    nullifierKeyCommitment := obj.nullifierKeyCommitment!}

/-- Converts Object to a Resource. Requires object's `nonce` to be set beforehand. -/
def Object.toResource {lab : Class.Label} (obj : Object lab) (ephemeral : Bool) (nonce : Anoma.Nonce) : Anoma.Resource
 := obj.toSomeObject.toResource ephemeral nonce

def Object.fromResource
  {lab : Class.Label}
  (res : Anoma.Resource)
  : Option (Object lab) := do
  let privateFields : lab.PrivateFields.type ← SomeType.cast res.value
  pure { quantity := res.quantity,
         nullifierKeyCommitment := res.nullifierKeyCommitment,
         nonce := res.nonce,
         privateFields := privateFields }

def SomeObject.fromResource
  (res : Anoma.Resource)
  : Option SomeObject := do
  let resLab : Object.Resource.Label ← tryCast res.label
  let lab : Class.Label := resLab.classLabel
  match @Object.fromResource lab res with
  | none => none
  | some obj => pure {label := lab, object := obj}
