import AVM.Class.Member
import AVM.Class.Label
import AVM.Ecosystem.Label

namespace AVM

structure FunctionData : Type where
  numConstructed : Nat
  numDestroyed : Nat
  numSelvesDestroyed : Nat

def Ecosystem.Label.MemberId.Data {lab : Ecosystem.Label} : lab.MemberId → Type
  | .functionId _ => FunctionData
  | _ => PUnit

/-- The app data for an object in a given class consists of:
    1. member logic indicator (indicator which member is being called)
    2. member arguments
  -/
structure AppData (lab : Ecosystem.Label) where
  memberId : lab.MemberId
  memberData : memberId.Data
  memberArgs : memberId.Args.type

structure SomeAppData where
  {label : Ecosystem.Label}
  appData : AppData label

def AppData.toSomeAppData {lab : Ecosystem.Label} (appData : AppData lab) : SomeAppData := {appData}

instance AppData.hasBEq {lab : Ecosystem.Label} : BEq (AppData lab) where
  beq a b :=
    a.memberId == b.memberId
    && a.memberArgs === b.memberArgs

instance AppData.hasTypeRep {lab : Ecosystem.Label} : TypeRep (AppData lab) where
  rep := Rep.composite "AVM.Class.AppData" [Rep.atomic lab.name]

instance SomeAppData.hasBeq : BEq SomeAppData where
  beq a b := a.appData === b.appData

instance SomeAppData.hasTypeRep : TypeRep SomeAppData where
  rep := Rep.atomic "AVM.Class.SomeAppData"

abbrev Logic.Args (lab : Ecosystem.Label) := Anoma.Logic.Args (AppData lab)
