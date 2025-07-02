
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
  [repArgs : TypeRep Args]
  [beqArgs : BEq Args]
  /-- The logic associated with the member being called. In a real
      implementation, this would be an enum indicating the logic to be used. In
      Lean, it is more convenient to have this as a function to avoid
      type-checking problems. -/
  memberLogic : Anoma.Logic.Args (Class.Member.AppData pub Args) → Bool
  memberAppData : Class.Member.AppData pub Args

instance instBeqAppData {pub : Public} : BEq (Class.AppData pub) where
  beq a b :=
    let _ := pub.beqPublicFields
    let _ := a.repArgs
    let _ := b.repArgs
    let _ := b.beqArgs
    -- TODO: check member logic properly
    a.memberAppData.publicFields == b.memberAppData.publicFields
    && beqCast a.memberAppData.args b.memberAppData.args

structure Class.SomeAppData where
  {pub : Public}
  appData : Class.AppData pub

instance instSomeAppDataBeq : BEq Class.SomeAppData where
  beq a b :=
    let _ := b.pub.beqPublicFields
    let _ := a.pub.repPublicFields
    let _ := b.pub.repPublicFields
    let _ := a.appData.repArgs
    let _ := b.appData.repArgs
    let _ := b.appData.beqArgs
    -- TODO: check member logic properly
    beqCast a.appData.memberAppData.publicFields b.appData.memberAppData.publicFields
    && beqCast a.appData.memberAppData.args b.appData.memberAppData.args

def Class.AppData.toSomeAppData {pub : Public} (appData : Class.AppData pub) : Class.SomeAppData := {appData}

instance instSomeAppDataTypeRep : TypeRep Class.SomeAppData where
  -- TODO: proper type representation
  rep := Rep.atomic "Goose.Class.SomeAppData"

end Goose
