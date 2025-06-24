
import Goose.Object
import Anoma.Resource

namespace Goose

/-- Syntax-level object description (fields + constructors + methods) should
  desugar to the `Class` structure. -/
structure Class where
  PrivateData : Type
  PublicData : Type
  [rawPrivateData : Anoma.Raw PrivateData]
  [rawPublicData : Anoma.Raw PublicData]
  /-- The `label` goes into the `classLabel` field of each object in the class.
    -/
  label : String
  constructors : List Object.Constructor
  methods : List Object.Method
  /-- Extra class-specific logic. The whole resource logic function for an
     object consists of the class logic and the method and constructor logics.
     -/
  extraLogic : Object → Anoma.Logic.Args (Object.AppData PublicData) → Bool

end Goose
