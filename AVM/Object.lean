
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
  rep := Rep.atomic ("AVM.Object" ++ lab.name)

structure SomeObject : Type (u + 1) where
  {lab : Class.Label.{u}}
  object : Object.{u} lab

instance SomeObject.hasTypeRep : TypeRep SomeObject where
  rep := Rep.atomic "AVM.SomeObject"

instance SomeObject.hasBEq : BEq SomeObject where
  beq a b := a.lab === b.lab && a.object === b.object

def Object.toSomeObject {lab : Class.Label} (object : Object lab) : SomeObject := {object}

def SomeObject.toResource (sobj : SomeObject)
    (ephemeral := false) (nonce := 0)
    : Anoma.Resource :=
    let lab := sobj.lab
    let obj := sobj.object
  { Val := lab.PrivateFields,
    Label := ⟨Class.Label × lab.DynamicLabel.dynLabel⟩,
    label := ⟨lab, lab.DynamicLabel.mkDynamicLabel obj.publicFields obj.privateFields⟩,
    quantity := obj.quantity,
    value := obj.privateFields,
    ephemeral := ephemeral,
    nonce,
    nullifierKeyCommitment := obj.nullifierKeyCommitment.getD Anoma.NullifierKeyCommitment.universal}

def Object.fromResource
  {lab : Class.Label}
  (publicFields : lab.PublicFields.type)
  (res : Anoma.Resource)
  : Option (Object lab) := do
  let privateFields : lab.PrivateFields.type <- SomeType.cast res.value
  pure { quantity := res.quantity,
         nullifierKeyCommitment := res.nullifierKeyCommitment,
         privateFields := privateFields,
         publicFields := publicFields }

def SomeObject.fromResource
  {PublicFields : SomeType}
  (publicFields : PublicFields.type)
  (res : Anoma.Resource)
  : Option SomeObject := do
  let lab : Class.Label ← tryCast res.label
  let lab' := {lab with PublicFields := PublicFields}
  match @Object.fromResource lab' publicFields res with
  | none => none
  | some obj => pure {lab := lab', object := obj}
