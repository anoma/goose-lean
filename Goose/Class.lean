
import Goose.Class.Member
import Goose.Signature

namespace Goose

/-- Syntax-level object description (fields + constructors + methods) should
    desugar to the `Class` structure. -/
structure Class (sig : Signature) where
  constructors : (c : sig.ConstructorId) -> Class.Constructor c
  methods : (m : sig.MethodId) -> Class.Method m
  /-- Extra class-specific logic. The whole resource logic function for an
     object consists of the class logic and the method and constructor logics.
     -/
  extraLogic : (self : Object sig) → Anoma.Logic.Args sig.pub.PublicFields → Bool

/-- The class app data consists of member logic (indicator which member is being
    called) and member app data. -/
structure Class.AppData (sig : Signature) where
  publicFields : sig.pub.PublicFields
  memberSomeAppData : Option (Class.Member.SomeAppData sig)
  -- TODO the types should reflect these three cases:
  -- 1. Class (consumed or created) => only public fields
  -- 2. Member created => only public fields
  -- 3. Member consumed => public fields + method args

instance instBeqAppData {sig : Signature} : BEq (Class.AppData sig) where
  beq a b :=
    let _ := sig.pub.beqPublicFields
    -- TODO: check member logic properly
    a.publicFields == b.publicFields
    && (match a.memberSomeAppData, b.memberSomeAppData with
      | some a', some b' => beqCast a' b'
      | _, _ => False)

structure Class.SomeAppData where
  {sig : Signature}
  appData : Class.AppData sig

instance instAppDataTypeRep {sig : Signature} : TypeRep (Class.AppData sig) where
  -- TODO: proper type representation
  rep := Rep.atomic "Goose.Class.AppData"

instance instSomeAppDataBeq : BEq Class.SomeAppData where
  beq a b :=
    -- TODO: check member logic properly
    beqCast a.appData b.appData

def Class.AppData.toSomeAppData {sig : Signature} (appData : Class.AppData sig) : Class.SomeAppData := {appData}

instance instSomeAppDataTypeRep : TypeRep Class.SomeAppData where
  -- TODO: proper type representation
  rep := Rep.atomic "Goose.Class.SomeAppData"

end Goose
