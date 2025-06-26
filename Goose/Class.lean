
import Goose.Class.Member

namespace Goose

/-- Syntax-level object description (fields + constructors + methods) should
    desugar to the `Class` structure. -/
structure Class where
  PrivateFields : Type
  PublicFields : Type
  [rawPrivateFields : Anoma.Raw PrivateFields]
  [rawPublicFields : Anoma.Raw PublicFields]
  /-- The `label` goes into the `classLabel` field of each object in the class.
    -/
  label : String
  constructors : List Class.Constructor
  methods : List Class.Method
  /-- Extra class-specific logic. The whole resource logic function for an
     object consists of the class logic and the method and constructor logics.
     -/
  extraLogic : (self : Object) → Anoma.Logic.Args (Class.Member.AppData Unit) → Bool

/-- The class app data consists of member logic (indicator which member is being
    called) and member app data. -/
structure Class.AppData where
  Args : Type
  [rawArgs : Anoma.Raw Args]
  /-- The logic associated with the member being called. In a real
      implementation, this would be an enum indicating the logic to be used. In
      Lean, it is more convenient to have this as a function to avoid
      type-checking problems. -/
  memberLogic : Anoma.Logic.Args (Class.Member.AppData Args) → Bool
  memberAppData : Class.Member.AppData Args

instance Class.AppData.RawInstance : Anoma.Raw Class.AppData where
  -- NOTE: this should also include a raw representation of the action logic
  raw appData := (@Member.AppData.RawInstance _ appData.rawArgs).raw appData.memberAppData
  cooked (_ : String) : Option Class.AppData :=  none

end Goose
