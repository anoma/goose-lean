import Prelude

namespace Anoma

/-- A secret value. Used to assign ownership to a Resource -/
inductive NullifierKey where
  /-- Everyone knows this key -/
  | universal : NullifierKey
  | secret : Nat → NullifierKey
  deriving Repr, BEq, Hashable

/-- Commitment to a nullifierkey. Used to prove that you own a NullifierKey without revealing it -/
inductive NullifierKeyCommitment where
  /-- Commitment of the universal NullifierKey -/
  | universal : NullifierKeyCommitment
  /-- The commitment of a secret key. Pattern matching on the argument should
  only be done by internal functions in this file -/
  | ofSecret : (privateNat : Nat) → NullifierKeyCommitment
  deriving Repr, BEq, Hashable, DecidableEq

instance NullifierKeyCommitment.instInhabited : Inhabited NullifierKeyCommitment where
  default := .universal

def checkNullifierKey (nk : NullifierKey) (nfc : NullifierKeyCommitment) : Bool :=
  match nk, nfc with
   | .universal, .universal => true
   | .secret k1, .ofSecret k2 => k1 == k2
   | _, _ => false

/-- Computes the commitment of a NullifierKey -/
def NullifierKey.commitment (k : NullifierKey) : NullifierKeyCommitment :=
  match k with
  | .universal => .universal
  | (.secret s) => .ofSecret s

/-- A public value derived from a secret NullifierKey and a Resource -/
inductive Nullifier where
  | privateMk : Nullifier
  deriving Repr, BEq, Hashable

/-- Temporary nullifier that should eventually be replaced with a proper one -/
def Nullifier.todo : Nullifier := privateMk

instance : TypeRep NullifierKeyCommitment where
  rep := Rep.atomic "NullifierKeyCommitment"
