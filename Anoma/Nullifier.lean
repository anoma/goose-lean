import Prelude

namespace Anoma

/-- A secret value. Used to assign ownership to a Resource -/
inductive NullifierKey where
  | privateMk : NullifierKey
  deriving Repr, BEq, Hashable

/-- Everyone knows this key -/
def NullifierKey.universal : NullifierKey := privateMk

/-- Commitment to a nullifierkey. Used to prove that you own a NullifierKey without revealing it -/
inductive NullifierKeyCommitment where
  | privateMk : NullifierKeyCommitment
  deriving Repr, BEq, Hashable, DecidableEq

/-- Not a secret. Use this instance when ownership is not relevant -/
instance NullifierKeyCommitment.instInhabited : Inhabited NullifierKeyCommitment where
  default := NullifierKeyCommitment.privateMk

/-- Computes the commitment of a NullifierKey -/
def commitment (_k : NullifierKey) : NullifierKeyCommitment := default

/-- A public value derived from a secret NullifierKey and a Resource -/
inductive Nullifier where
  | privateMk : Nullifier
  deriving Repr, BEq, Hashable

/-- Temporary nullifier that should eventually be replaced with a proper one -/
def Nullifier.todo : Nullifier := privateMk

instance : TypeRep NullifierKeyCommitment where
  rep := Rep.atomic "NullifierKeyCommitment"

/-- Not a secret. Use this instance when ownership is not relevant -/
instance NullifierKey.instInhabited : Inhabited NullifierKey where
  default := NullifierKey.privateMk

/-- Use this when the nullifier key is universal -/
def NullifierKeyCommitment.universal : NullifierKeyCommitment := default
