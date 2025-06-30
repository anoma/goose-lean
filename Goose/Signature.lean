import Anoma.Resource
import Prelude

namespace Goose

structure Private where
  PrivateFields : Type
  [repPrivateFields : TypeRep PrivateFields]

structure Public where
  PublicFields : Type
  [repPublicFields : TypeRep PublicFields]

structure Signature where
  priv : Private
  pub : Public
  classLabel : String
