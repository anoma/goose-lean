
import Anoma.Resource
import Goose.Signature

namespace Goose

/-- Represents a concrete object, translated into a resource. For class
    represetation (object description), see `Goose.Class`. -/
structure Object (sig : Signature) where
  quantity : Nat
  /-- `privateFields` go into the `value` field of the resource -/
  privateFields : Private.PrivateFields sig.priv
  /-- `publicFields` go into the `appData` field of the action -/
  publicFields : Public.PublicFields sig.pub

structure SomeObject where
  {sig : Signature}
  object : Object sig

def Object.toSomeObject {sig : Signature} (object : Object sig) : SomeObject := {object}

def SomeObject.toResource (sobj : SomeObject)
    (ephemeral := false) (nonce := 0) (nullifierKeyCommitment := "")
    : Anoma.Resource :=
    let sig := sobj.sig
    let obj := sobj.object
  { Val := sig.priv.PrivateFields,
    repVal :=  sig.priv.repPrivateFields,
    beqVal := sig.priv.beqPrivateFields,
    label := sig.classLabel,
    -- NOTE: in general, there may be more things in the label, not necessarily statically determined
    quantity := obj.quantity,
    value := obj.privateFields,
    ephemeral := ephemeral,
    nonce,
    nullifierKeyCommitment }

def Object.fromResource
  {sig : Signature}
  (publicFields : sig.pub.PublicFields )
  (res : Anoma.Resource)
  : Option (Object sig) :=
  let _ : TypeRep res.Val := res.repVal
  let _ : TypeRep sig.priv.PrivateFields := sig.priv.repPrivateFields
  do
  let privateFields : sig.priv.PrivateFields <- tryCast res.value
  pure { quantity := res.quantity,
         privateFields := privateFields,
         publicFields := publicFields }

def SomeObject.fromResource
  (pub : Public)
  (pubVals : pub.PublicFields)
  (res : Anoma.Resource)
  : SomeObject where
    sig := {
      priv := { PrivateFields := res.Val
                repPrivateFields := res.repVal
                beqPrivateFields := res.beqVal
               }
      pub := pub
      classLabel := res.label
     }
    object := {
      quantity := res.quantity
      privateFields := res.value
      publicFields := pubVals
     }

end Goose
