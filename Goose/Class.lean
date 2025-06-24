
import Goose.Object
import Anoma.Resource

namespace Goose

structure Class where
  PrivateData : Type
  PublicData : Type
  [rawPrivateData : Anoma.Raw PrivateData]
  [rawPublicData : Anoma.Raw PublicData]
  label : String
  constructors : List Object.Constructor
  methods : List Object.Method
  /-- Extra class-specific logic. The whole resource logic function for an
     object consists of the class logic and the method and constructor logics.
     -/
  extraLogic : Object → Anoma.Logic.Args (Object.AppData PublicData) → Bool

end Goose
