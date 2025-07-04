
import AVM.Class.Member
import AVM.Class.Label

namespace AVM

/-- Syntax-level object description (fields + constructors + methods) should
    desugar to the `Class` structure. -/
structure Class (lab : Class.Label) where
  constructors : (c : lab.ConstructorId) -> Class.Constructor c
  methods : (m : lab.MethodId) -> Class.Method m
  /-- Extra class-specific logic. The whole resource logic function for an
     object consists of the class logic and the method and constructor logics.
     -/
  extraLogic : (self : Object lab) → Anoma.Logic.Args lab.pub.PublicFields → Bool

/-- The class app data consists of:
    1. public fields of the object
    2. member logic indicator (indicator which member is being
      called)
    3. member arguments
  -/
structure Class.AppData (lab : Label) where
  publicFields : lab.pub.PublicFields
  memberId : lab.MemberId
  memberArgs : memberId.Args

instance Class.AppData.hasBEq {lab : Label} : BEq (Class.AppData lab) where
  beq a b :=
    let _ := lab.pub.beqPublicFields
    -- TODO: check member logic properly
    a.publicFields == b.publicFields
    && a.memberId == b.memberId
    && beqCast a.memberArgs b.memberArgs

structure Class.SomeAppData where
  {lab : Label}
  appData : Class.AppData lab

instance Class.AppData.hasTypeRep {lab : Label} : TypeRep (Class.AppData lab) where
  -- TODO: proper type representation
  rep := Rep.atomic "AVM.Class.AppData"

instance SomeAppData.hasBeq : BEq Class.SomeAppData where
  beq a b :=
    -- TODO: check member logic properly
    beqCast a.appData b.appData

def Class.AppData.toSomeAppData {lab : Label} (appData : Class.AppData lab) : Class.SomeAppData := {appData}

instance instSomeAppDataTypeRep : TypeRep Class.SomeAppData where
  -- TODO: proper type representation
  rep := Rep.atomic "AVM.Class.SomeAppData"

end AVM
