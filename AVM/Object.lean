
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

def SomeObject.toResource (sobj : SomeObject)
    (ephemeral : Bool) (nonce := 0)
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

def Object.toResource {lab : Class.Label} (obj : Object lab) (ephemeral : Bool) : Anoma.Resource
 := obj.toSomeObject.toResource ephemeral

structure ConsumableObject (lab : Class.Label) where
  object : Object lab
  ephemeral : Bool
  key : Anoma.NullifierKey
  deriving BEq

structure ConsumedObject (lab : Class.Label) extends ConsumableObject lab where
  nullifierProof : Anoma.NullifierProof key (object.toResource ephemeral)

def ConsumedObject.toConsumable {lab : Class.Label} (c : ConsumedObject lab) : ConsumableObject lab :=
 { object := c.object
   ephemeral := c.ephemeral
   key := c.key }

instance ConsumedObject.instBEq {lab : Class.Label} : BEq (ConsumedObject lab) where
  beq a b := BEq.beq a.toConsumable b.toConsumable

instance ConsumedObject.hasTypeRep (lab : Class.Label) : TypeRep (ConsumedObject lab) where
  rep := Rep.atomic ("AVM.ConsumedObject_" ++ lab.name)

structure SomeConsumedObject where
  {label : Class.Label}
  consumed : ConsumedObject label

instance SomeConsumedObject.hasBEq : BEq SomeConsumedObject where
  beq a b := a.label === b.label && a.consumed === b.consumed

instance SomeConsumedObject.hasTypeRep : TypeRep SomeConsumedObject where
  rep := Rep.atomic "AVM.SomeConsumedObject"

def ConsumedObject.resource {lab : Class.Label} (c : ConsumedObject lab) : Anoma.Resource :=
  c.object.toResource c.ephemeral

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

def Object.toConsumable {lab : Class.Label} (object : Object lab) (ephemeral : Bool) (key : Anoma.NullifierKey) : ConsumableObject lab where
  object
  key
  ephemeral

def ConsumableObject.resource {lab : Class.Label} (c : ConsumableObject lab) : Anoma.Resource := c.object.toResource c.ephemeral

def ConsumableObject.consume {lab : Class.Label} (c : ConsumableObject lab) : Option (ConsumedObject lab) :=
  let resource := c.object.toResource c.ephemeral
  match Anoma.nullify c.key resource with
  | isFalse _ => none
  | isTrue null => pure
       { object := c.object
         ephemeral := c.ephemeral
         key := c.key
         nullifierProof := null }

def ConsumedObject.toRootedNullifiableResource {lab : Class.Label} (c : ConsumedObject lab) : Anoma.RootedNullifiableResource where
  key := c.key
  resource := c.resource
  nullifierProof := c.nullifierProof
  root := Anoma.CommitmentRoot.todo

def SomeConsumedObject.toRootedNullifiableResource (sconsumed : SomeConsumedObject) : Anoma.RootedNullifiableResource :=
  sconsumed.consumed.toRootedNullifiableResource

def SomeConsumedObject.toSomeObject (sconsumed : SomeConsumedObject) : SomeObject :=
  ⟨sconsumed.consumed.object⟩
