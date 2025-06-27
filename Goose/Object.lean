
import Anoma.Raw
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

abbrev SomeObject := Σ (sig : Signature), Object sig

def Object.toSomeObject {sig : Signature} (obj : Object sig) : SomeObject := ⟨sig, obj⟩

def SomeObject.toResource (sobj : SomeObject)
    (ephemeral := false) (nonce := 0) (nullifierKeyCommitment := "")
    : Anoma.Resource :=
    let ⟨sig, obj⟩ := sobj
  { Val := sig.priv.PrivateFields,
    rawVal :=  sig.priv.rawPrivateFields,
    label := sig.classLabel,
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
  let _ : Anoma.Raw res.Val := res.rawVal
  let _ : Anoma.Raw sig.priv.PrivateFields := sig.priv.rawPrivateFields
  do
  let privateFields : sig.priv.PrivateFields <- Anoma.Raw.cooked (Anoma.Raw.raw res.value) -- TODO this cast should be done safely
  pure { quantity := res.quantity,
         privateFields := privateFields,
         publicFields := publicFields }

def SomeObject.fromResource
  (pub : Public)
  (pubVals : pub.PublicFields)
  (res : Anoma.Resource)
  : SomeObject where
  fst := {
    priv := { PrivateFields := res.Val
              rawPrivateFields := res.rawVal
             }
    pub := pub
    classLabel := res.label
   }
  snd := {
    quantity := res.quantity
    privateFields := res.value
    publicFields := pubVals
   }

end Goose
