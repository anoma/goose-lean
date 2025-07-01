import Anoma.Resource
import Prelude

namespace Goose

structure Private where
  PrivateFields : Type
  [repPrivateFields : TypeRep PrivateFields]
  [beqPrivateFields : BEq PrivateFields]

structure Public where
  PublicFields : Type
  [repPublicFields : TypeRep PublicFields]
  [beqPublicFields : BEq PublicFields]

instance instBeqPrivate : BEq Private where
  beq a b :=
    let _ := a.repPrivateFields
    let _ := b.repPrivateFields
    TypeRep.rep a.PrivateFields == TypeRep.rep b.PrivateFields

instance instBeqPublic : BEq Public where
  beq a b :=
    let _ := a.repPublicFields
    let _ := b.repPublicFields
    TypeRep.rep a.PublicFields == TypeRep.rep b.PublicFields

-- TODO rename to something that does not conflict with authorization
structure Signature where
  priv : Private
  pub : Public
  classLabel : String
deriving BEq
