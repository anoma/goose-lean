
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

/-- The app data for an object in a given class consists of:
    1. member logic indicator (indicator which member is being called)
    2. member arguments
    3. public fields of the object
  -/
structure Class.AppData (lab : Label) where
  memberId : lab.MemberId
  memberArgs : memberId.Args
  publicFields : lab.pub.PublicFields

structure Class.SomeAppData where
  {lab : Label}
  appData : Class.AppData lab

def Class.AppData.toSomeAppData {lab : Label} (appData : Class.AppData lab) : Class.SomeAppData := {appData}

instance Class.AppData.hasBEq {lab : Label} : BEq (Class.AppData lab) where
  beq a b :=
    let _ := lab.pub.beqPublicFields
    let _ := Label.MemberId.Args.hasTypeRep a.memberId
    let _ := Label.MemberId.Args.hasTypeRep b.memberId
    let _ := Label.MemberId.Args.hasBeq b.memberId
    a.publicFields == b.publicFields
    && a.memberId == b.memberId
    && a.memberArgs === b.memberArgs

instance Class.AppData.hasTypeRep {lab : Label} : TypeRep (Class.AppData lab) where
  rep := Rep.atomic ("AVM.Class.AppData_" ++ lab.name)

instance SomeAppData.hasBeq : BEq Class.SomeAppData where
  beq a b := a.appData === b.appData

instance SomeAppData.hasTypeRep : TypeRep Class.SomeAppData where
  rep := Rep.atomic "AVM.Class.SomeAppData"

end AVM
