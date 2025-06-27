
import Goose.Class.Member
import Goose.Signature

namespace Goose

/-- Syntax-level object description (fields + constructors + methods) should
    desugar to the `Class` structure. -/
structure Class (sig : Signature) where
  constructors : List (Class.Constructor sig)
  methods : List (Class.Method sig)
  /-- Extra class-specific logic. The whole resource logic function for an
     object consists of the class logic and the method and constructor logics.
     -/
  extraLogic : (self : Object sig) → Anoma.Logic.Args (Class.Member.AppData sig.pub Unit) → Bool

/-- The class app data consists of member logic (indicator which member is being
    called) and member app data. -/
structure Class.AppData (pub : Public) where
  Args : Type
  [rawArgs : Anoma.Raw Args]
  /-- The logic associated with the member being called. In a real
      implementation, this would be an enum indicating the logic to be used. In
      Lean, it is more convenient to have this as a function to avoid
      type-checking problems. -/
  memberLogic : Anoma.Logic.Args (Class.Member.AppData pub Args) → Bool
  memberAppData : Class.Member.AppData pub Args

abbrev Class.SomeAppData := Σ (pub : Public), Class.AppData pub

def Class.AppData.toSomeAppData {pub : Public} (a : Class.AppData pub) : Class.SomeAppData := ⟨pub, a⟩

instance Class.SomeAppData.RawInstance : Anoma.Raw Class.SomeAppData where
  -- NOTE: this should also include a raw representation of the action logic
  raw x :=
   let appData := x.2
   (@Member.AppData.RawInstance _ _ appData.rawArgs).raw appData.memberAppData
  cooked := panic! "cooked"

instance Class.AppData.RawInstance (pub : Public) : Anoma.Raw (Class.AppData pub) where
  raw appData := Anoma.Raw.raw appData.toSomeAppData
  cooked := panic! "cooked"

end Goose
