import AVM.Class.Member
import AVM.Class.Label
import AVM.Ecosystem.Label

namespace AVM.Ecosystem

/-- The app data for an object in a given class consists of:
    1. member logic indicator (indicator which member is being called)
    2. member arguments
  -/
structure AppData (lab : EcosystemLabel) where
  memberId : lab.MemberId
  memberArgs : memberId.Args.type

structure SomeAppData where
  {label : EcosystemLabel}
  appData : AppData label

def AppData.toSomeAppData {lab : EcosystemLabel} (appData : AppData lab) : SomeAppData := {appData}

instance AppData.hasBEq {lab : EcosystemLabel} : BEq (AppData lab) where
  beq a b :=
    a.memberId == b.memberId
    && a.memberArgs === b.memberArgs

instance AppData.hasTypeRep {lab : EcosystemLabel} : TypeRep (AppData lab) where
  rep := Rep.composite "AVM.Class.AppData" [Rep.atomic lab.name]

instance SomeAppData.hasBeq : BEq SomeAppData where
  beq a b := a.appData === b.appData

instance SomeAppData.hasTypeRep : TypeRep SomeAppData where
  rep := Rep.atomic "AVM.Class.SomeAppData"

abbrev Logic.Args (lab : EcosystemLabel) := Anoma.Logic.Args (AppData lab)
