
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
  extraLogic : (self : Object) → Anoma.Logic.Args (Object.AppData Unit) → Bool

/-- The appData associated with a class consists of action logic (indicator
  which action is being performed) and object app data. -/
structure Class.AppData where
  Args : Type
  [rawArgs : Anoma.Raw Args]
  /-- The logic associated with the action being performed (method or
          constructor call). In a real implementation, this would be an enum
          indicating the logic to be used. In Lean, it is more convenient to
          have this as a function to avoid type-checking problems. -/
  actionLogic : Anoma.Logic.Args (Object.AppData Args) → Bool
  objectAppData : Object.AppData Args

instance Class.AppData.RawInstance : Anoma.Raw Class.AppData where
  -- NOTE: this should also include a raw representation of the action logic
  raw appData := (@Object.AppData.RawInstance _ appData.rawArgs).raw appData.objectAppData

end Goose
