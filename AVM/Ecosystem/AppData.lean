import AVM.Ecosystem.Label

namespace AVM

structure MultiMethodData : Type where
  numConstructed : Nat
  numDestroyed : Nat
  numSelvesDestroyed : Nat
  numReassembledNewUid : Nat
  numReassembledOldUid : Nat
  deriving BEq

instance Nonce.hasTypeRep : TypeRep MultiMethodData where
  rep := Rep.atomic "AVM.MultiMethodData"

structure MultiMethodRandoms (d : MultiMethodData) where
  destroyedEphRands : List.Vector Nat d.numDestroyed
  /-- The nonce is also used for uid -/
  constructedNonces : List.Vector Anoma.Nonce d.numConstructed
  constructedRands : List.Vector Nat d.numConstructed
  reassembledNewUidRands : List.Vector Nat d.numReassembledNewUid
  reassembledNewUidNonces : List.Vector Anoma.Nonce d.numReassembledNewUid
  reassembledOldUidRands : List.Vector Nat d.numReassembledOldUid
  selvesDestroyedEphRands : List.Vector Nat d.numSelvesDestroyed

def Ecosystem.Label.MemberId.Data {lab : Ecosystem.Label} : lab.MemberId → Type
  | .multiMethodId _ => MultiMethodData
  | _ => Unit

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

