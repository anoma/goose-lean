
import AVM.Class.Member
import AVM.Class.Label

namespace AVM.Class

/-- The app data for an object in a given class consists of:
    1. member logic indicator (indicator which member is being called)
    2. member arguments
    3. public fields of the object
  -/
structure AppData (lab : Label) where
  memberId : lab.MemberId
  memberArgs : memberId.Args.type
  publicFields : lab.PublicFields.type

structure SomeAppData where
  {lab : Label}
  appData : Class.AppData lab

def AppData.toSomeAppData {lab : Label} (appData : Class.AppData lab) : Class.SomeAppData := {appData}

instance AppData.hasBEq {lab : Label} : BEq (Class.AppData lab) where
  beq a b :=
    a.publicFields === b.publicFields
    && a.memberId == b.memberId
    && a.memberArgs === b.memberArgs

instance AppData.hasTypeRep {lab : Label} : TypeRep (Class.AppData lab) where
  rep := Rep.atomic ("AVM.Class.AppData_" ++ lab.name)

instance SomeAppData.hasBeq : BEq Class.SomeAppData where
  beq a b := a.appData === b.appData

instance SomeAppData.hasTypeRep : TypeRep Class.SomeAppData where
  rep := Rep.atomic "AVM.Class.SomeAppData"

abbrev Logic.Args (lab : Label) := Anoma.Logic.Args (Class.AppData lab)

def SomeObject.fromResource
  (someAppData : SomeAppData)
  (res : Anoma.Resource)
  : Option SomeObject := do
  let lab : Class.Label ← tryCast res.label
  match SomeType.cast someAppData.appData.publicFields with
  | none => none
  | some (publicFields : lab.PublicFields.type) =>
    match Object.fromResource publicFields res with
    | none => none
    | some obj => pure {lab := lab, object := obj}
