
import Anoma.Resource
import AVM.Class.Label

namespace AVM

/-- Represents a concrete object, translated into a resource. For class
    represetation (object description), see `AVM.Class`. -/
structure Object (lab : Class.Label) where
  /-- Used to prove ownership -/
  nullifierKeyCommitment : Option Anoma.NullifierKeyCommitment
  quantity : Nat
  /-- `privateFields` go into the `value` field of the resource -/
  privateFields : lab.PrivateFields.type
  /-- `publicFields` go into the `appData` field of the action -/
  publicFields : lab.PublicFields.type
  deriving BEq

instance Object.hasTypeRep (lab : Class.Label) : TypeRep (Object lab) where
  rep := Rep.atomic ("AVM.Object_" ++ lab.name)

structure SomeObject where
  {label : Class.Label}
  object : Object label

instance SomeObject.hasTypeRep : TypeRep SomeObject where
  rep := Rep.atomic "AVM.SomeObject"

instance SomeObject.hasBEq : BEq SomeObject where
  beq a b := a.label === b.label && a.object === b.object

def Object.nullifierKeyCommitment! {lab : Class.Label} (o : Object lab) : Anoma.NullifierKeyCommitment :=
  o.nullifierKeyCommitment.getD Anoma.NullifierKeyCommitment.universal

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

def SomeObject.toResource (sobj : SomeObject)
    (ephemeral := false) (nonce := 0)
    : Anoma.Resource :=
  let lab := sobj.label
  let obj := sobj.object
  { Val := lab.PrivateFields,
    Label := ⟨Object.Resource.Label⟩,
    label := ⟨lab, lab.DynamicLabel.mkDynamicLabel obj.privateFields⟩,
    quantity := obj.quantity,
    value := obj.privateFields,
    ephemeral := ephemeral,
    nonce,
    nullifierKeyCommitment := obj.nullifierKeyCommitment!}

def Object.fromResource
  {lab : Class.Label}
  (publicFields : lab.PublicFields.type)
  (res : Anoma.Resource)
  : Option (Object lab) := do
  let privateFields : lab.PrivateFields.type ← SomeType.cast res.value
  pure { quantity := res.quantity,
         nullifierKeyCommitment := res.nullifierKeyCommitment,
         privateFields := privateFields,
         publicFields := publicFields }

def SomeObject.fromResource
  {PublicFields : SomeType}
  (publicFields : PublicFields.type)
  (res : Anoma.Resource)
  : Option SomeObject := do
  let resLab : Object.Resource.Label ← tryCast res.label
  let lab : Class.Label := resLab.classLabel
  let lab' := {lab with PublicFields := PublicFields}
  match @Object.fromResource lab' publicFields res with
  | none => none
  | some obj => pure {label := lab', object := obj}
