
import Anoma.Resource
import Goose.Class.Label

namespace Goose

/-- Represents a concrete object, translated into a resource. For class
    represetation (object description), see `Goose.Class`. -/
structure Object (lab : Class.Label) where
  quantity : Nat
  /-- `privateFields` go into the `value` field of the resource -/
  privateFields : Class.Private.PrivateFields lab.priv
  /-- `publicFields` go into the `appData` field of the action -/
  publicFields : Class.Public.PublicFields lab.pub

structure SomeObject where
  {lab : Class.Label}
  object : Object lab

def Object.toSomeObject {lab : Class.Label} (object : Object lab) : SomeObject := {object}

def SomeObject.toResource (sobj : SomeObject)
    (ephemeral := false) (nonce := 0) (nullifierKeyCommitment := "")
    : Anoma.Resource :=
    let lab := sobj.lab
    let obj := sobj.object
  { Val := lab.priv.PrivateFields,
    repVal := lab.priv.repPrivateFields,
    beqVal := lab.priv.beqPrivateFields,
    Label := Class.Label,
    label := lab,
    -- NOTE: in general, there may be more things in the label, not necessarily statically determined
    quantity := obj.quantity,
    value := obj.privateFields,
    ephemeral := ephemeral,
    nonce,
    nullifierKeyCommitment }

def Object.fromResource
  {lab : Class.Label}
  (publicFields : lab.pub.PublicFields)
  (res : Anoma.Resource)
  : Option (Object lab) :=
  let _ : TypeRep res.Val := res.repVal
  let _ : TypeRep lab.priv.PrivateFields := lab.priv.repPrivateFields
  do
  let privateFields : lab.priv.PrivateFields <- tryCast res.value
  pure { quantity := res.quantity,
         privateFields := privateFields,
         publicFields := publicFields }

/-
def SomeObject.fromResource (res : Anoma.Resource) : Option SomeObject := do
  let _ : TypeRep res.Label := res.repLabel
  match tryCast res.label with
  | none => none
  | some lab =>
    match Object.fromResource sorry res with
    | none => none
    | some object =>
      pure { lab, object }
-/
