
import Anoma.Raw
import Anoma.Resource
import Goose.Signature

namespace SigGoose

/-- Represents a concrete object, translated into a resource. For class
    represetation (object description), see `Goose.Class`. -/
structure Object (sig : Signature) where
  quantity : Nat
  /-- `privateFields` go into the `value` field of the resource -/
  privateFields : Private.PrivateFields sig.priv
  /-- `publicFields` go into the `appData` field of the action -/
  publicFields : Public.PublicFields sig.pub

def Object.toResource {sig : Signature} (obj : Object sig)
    (ephemeral := false) (nonce := 0) (nullifierKeyCommitment := "")
    : Anoma.Resource :=
  { Val := Private.PrivateFields sig.priv,
    rawVal := Private.rawPrivateFields sig.priv,
    label := sig.classLabel,
    quantity := obj.quantity,
    value := obj.privateFields,
    ephemeral := ephemeral,
    nonce,
    nullifierKeyCommitment }

def Object.fromResource
  {sig : Signature}
  (publicFields : Public.PublicFields sig.pub)
  (res : Anoma.Resource)
  : Option (Object sig) :=
  let _ : Anoma.Raw res.Val := res.rawVal
  let _ : Anoma.Raw (Private.PrivateFields sig.priv) := Private.rawPrivateFields sig.priv
  do
  let privateFields : sig.priv.PrivateFields <- Anoma.Raw.cooked (Anoma.Raw.raw res.value)
  pure { quantity := res.quantity,
         privateFields := privateFields,
         publicFields := publicFields }

end SigGoose
