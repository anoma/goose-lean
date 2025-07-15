
import AVM.Class.Member
import AVM.Class.Label

namespace AVM.Class

/-- The app data for an object in a given class consists of:
    1. member logic indicator (indicator which member is being called)
    2. member arguments
  -/
structure AppData (lab : Label) where
  memberId : lab.MemberId
  memberArgs : memberId.Args.type

structure SomeAppData where
  {label : Label}
  appData : Class.AppData label

def AppData.toSomeAppData {lab : Label} (appData : Class.AppData lab) : Class.SomeAppData := {appData}

instance AppData.hasBEq {lab : Label} : BEq (Class.AppData lab) where
  beq a b :=
    a.memberId == b.memberId
    && a.memberArgs === b.memberArgs

instance AppData.hasTypeRep {lab : Label} : TypeRep (Class.AppData lab) where
  rep := Rep.composite "AVM.Class.AppData" [Rep.atomic lab.name]

instance SomeAppData.hasBeq : BEq Class.SomeAppData where
  beq a b := a.appData === b.appData

instance SomeAppData.hasTypeRep : TypeRep Class.SomeAppData where
  rep := Rep.atomic "AVM.Class.SomeAppData"

abbrev Logic.Args (lab : Label) := Anoma.Logic.Args (Class.AppData lab)
