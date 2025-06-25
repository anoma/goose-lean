
import Anoma.Raw
import Anoma.Resource

namespace Goose

/-- Represents a concrete object, translated into a resource. For class
    represetation (object description), see `Goose.Class`. -/
structure Object where
  PrivateFields : Type
  PublicFields : Type
  [rawPrivateFields : Anoma.Raw PrivateFields]
  [rawPublicFields : Anoma.Raw PublicFields]
  classLabel : String
  quantity : Nat
  /-- `privateFields` go into the `value` field of the resource -/
  privateFields : PrivateFields
  /-- `publicFields` go into the `appData` field of the action -/
  publicFields : PublicFields

def Object.toResource (obj : Object) (ephemeral := false) (nonce := 0) (nullifierKeyCommitment := "") : Anoma.Resource :=
  { Val := obj.PrivateFields,
    rawVal := obj.rawPrivateFields,
    label := obj.classLabel,
    quantity := obj.quantity,
    value := obj.privateFields,
    ephemeral := ephemeral,
    nonce,
    nullifierKeyCommitment }

def Object.fromResource {PublicFields} [Anoma.Raw PublicFields] (publicFields : PublicFields) (res : Anoma.Resource) : Object :=
  { PrivateFields := res.Val,
    PublicFields := PublicFields,
    rawPrivateFields := res.rawVal,
    quantity := res.quantity,
    privateFields := res.value,
    publicFields := publicFields,
    classLabel := res.label }

end Goose
