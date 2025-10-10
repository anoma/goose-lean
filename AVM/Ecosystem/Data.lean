import AVM.Ecosystem.Label.Base

namespace AVM

structure MultiMethodData : Type where
  numConstructed : Nat
  numSelvesDestroyed : Nat
  numReassembledNewUid : Nat
  numReassembledOldUid : Nat
  deriving BEq, Repr

instance Nonce.hasTypeRep : TypeRep MultiMethodData where
  rep := Rep.atomic "AVM.MultiMethodData"

structure MultiMethodRandoms (d : MultiMethodData) where
  /-- The nonce is also used for uid -/
  constructedNonces : List.Vector Anoma.Nonce d.numConstructed
  constructedRands : List.Vector Nat d.numConstructed
  reassembledNewUidRands : List.Vector Nat d.numReassembledNewUid
  reassembledNewUidNonces : List.Vector Anoma.Nonce d.numReassembledNewUid
  reassembledOldUidRands : List.Vector Nat d.numReassembledOldUid
  selvesDestroyedEphRands : List.Vector Nat d.numSelvesDestroyed
  deriving Inhabited
