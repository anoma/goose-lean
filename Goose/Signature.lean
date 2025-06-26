import Anoma.Raw
import Anoma.Resource

namespace Goose

structure Private where
  PrivateFields : Type
  [rawPrivateFields : Anoma.Raw PrivateFields]

structure Public where
  PublicFields : Type
  [rawPublicFields : Anoma.Raw PublicFields]

structure Signature where
  priv : Private
  pub : Public
  classLabel : String
