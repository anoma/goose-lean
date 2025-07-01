import Anoma.Raw
import Anoma.Resource

namespace Goose

structure Private where
  PrivateFields : Type
  [rawPrivateFields : Anoma.Raw PrivateFields]

structure Public where
  PublicFields : Type
  [rawPublicFields : Anoma.Raw PublicFields]

-- TODO rename to something that does not conflict with authorization
structure Signature where
  priv : Private
  pub : Public
  classLabel : String
