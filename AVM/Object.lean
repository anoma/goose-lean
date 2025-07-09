
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

structure ConsumedObject (lab : Class.Label) where
  object : Object lab
  resource : Anoma.Resource
  key : Anoma.NullifierKey
  nullifier : Anoma.Nullifier
  deriving BEq

instance ConsumedObject.hasTypeRep (lab : Class.Label) : TypeRep (ConsumedObject lab) where
  rep := Rep.atomic ("AVM.ConsumedObject_" ++ lab.name)

structure SomeConsumedObject where
  {label : Class.Label}
  consumed : ConsumedObject label

instance SomeConsumedObject.hasBEq : BEq SomeConsumedObject where
  beq a b := a.label === b.label && a.consumed === b.consumed

instance SomeConsumedObject.hasTypeRep : TypeRep SomeConsumedObject where
  rep := Rep.atomic "AVM.SomeConsumedObject"

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

def Object.toResource {lab : Class.Label} (obj : Object lab) : Anoma.Resource
 := obj.toSomeObject.toResource

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

def Object.consume {lab : Class.Label} (object : Object lab) (key : Anoma.NullifierKey) : Option (ConsumedObject lab) :=
  let resource := object.toResource
  match Anoma.nullify
        { key
          resource
          root := Anoma.CommitmentRoot.todo }
  with
  | none => none
  | (some nullifier) => pure
       { object
         resource
         key
         nullifier }

def SomeObject.consume (o : SomeObject) (key : Anoma.NullifierKey) : Option SomeConsumedObject :=
   let label := o.label
   match o.object.consume key with
   | none => none
   | (some consumed) => some { label
                               consumed }

def ConsumedObject.toRootedNullifiableResource {lab : Class.Label} (consumed : ConsumedObject lab) : Anoma.RootedNullifiableResource :=
  { key := consumed.key
    root := Anoma.CommitmentRoot.todo
    resource := consumed.resource }

def SomeConsumedObject.toRootedNullifiableResource (sconsumed : SomeConsumedObject) : Anoma.RootedNullifiableResource :=
  sconsumed.consumed.toRootedNullifiableResource

def SomeConsumedObject.toSomeObject (sconsumed : SomeConsumedObject) : SomeObject :=
  ⟨sconsumed.consumed.object⟩
