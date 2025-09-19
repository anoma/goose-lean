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
