
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

structure SomeObject : Type (u + 2) where
  {lab : Class.Label.{u}}
  object : Object.{u} lab

def Object.toSomeObject {lab : Class.Label} (object : Object lab) : SomeObject := {object}

def SomeObject.toResource (sobj : SomeObject)
    (ephemeral := false) (nonce := 0)
    : Anoma.Resource :=
    let lab := sobj.lab
    let obj := sobj.object
  { Val := lab.PrivateFields,
    Label := ⟨Class.Label⟩,
    label := lab,
    -- NOTE: in general, there may be more things in the label, not necessarily statically determined
    quantity := obj.quantity,
    value := obj.privateFields,
    ephemeral := ephemeral,
    nonce,
    nullifierKeyCommitment := obj.nullifierKeyCommitment.getD default}

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
