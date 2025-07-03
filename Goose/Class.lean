
import Goose.Class.Member
import Goose.Class.Label

namespace Goose

/-- Syntax-level object description (fields + constructors + methods) should
    desugar to the `Class` structure. -/
structure Class (lab : Class.Label) where
  constructors : (c : lab.ConstructorId) -> Class.Constructor c
  methods : (m : lab.MethodId) -> Class.Method m
  /-- Extra class-specific logic. The whole resource logic function for an
     object consists of the class logic and the method and constructor logics.
     -/
  extraLogic : (self : Object lab) → Anoma.Logic.Args lab.pub.PublicFields → Bool

/-- The class app data consists of member logic (indicator which member is being
    called) and member app data. -/
structure Class.AppData (lab : Label) where
  publicFields : lab.pub.PublicFields
  memberSomeAppData : Option (Class.Member.SomeAppData lab)
  -- TODO the types should reflect these three cases:
  -- 1. Class (consumed or created) => only public fields
  -- 2. Member created => only public fields
  -- 3. Member consumed => public fields + method args

instance Class.AppData.hasBEq {lab : Label} : BEq (Class.AppData lab) where
  beq a b :=
    let _ := lab.pub.beqPublicFields
    -- TODO: check member logic properly
    a.publicFields == b.publicFields
    && (match a.memberSomeAppData, b.memberSomeAppData with
      | some a', some b' => beqCast a' b'
      | _, _ => False)

structure Class.SomeAppData where
  {lab : Label}
  appData : Class.AppData lab

instance Class.AppData.hasTypeRep {lab : Label} : TypeRep (Class.AppData lab) where
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
