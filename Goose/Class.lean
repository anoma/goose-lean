
import Goose.Object

namespace Goose

structure Class where
  PrivateData : Type
  PublicData : Type
  [rawPrivateData : Anoma.Raw PrivateData]
  [rawPublicData : Anoma.Raw PublicData]
  label : String
  constructors : List Object.Constructor
  methods : List Object.Method

end Goose
