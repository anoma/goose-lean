namespace Anoma

/-- A secret value. Used to assign ownership to a Resource -/
inductive NullifierKey where
  | privateMk : NullifierKey
  deriving Repr, BEq, Hashable

namespace NullifierKey

/-- Not a secret. Use this instance when ownership is not relevant -/
instance NullifierKey.instInhabited : Inhabited NullifierKey where
  default := NullifierKey.privateMk

abbrev universal : NullifierKey := default

end NullifierKey

/-- A public value derived from a secret NullifierKey and a Resource -/
inductive Nullifier where
  | privateMk : Nullifier
  deriving Repr, BEq, Hashable

def Nullifier.placeholder : Nullifier := privateMk

/-- Commitment to a nullifierkey. Used to prove that you own a NullifierKey without revealing it -/
inductive NullifierKeyCommitment where
  | privateMk : NullifierKeyCommitment
  deriving Repr, BEq, Hashable

/-- Not a secret. Use this instance when ownership is not relevant -/
instance NullifierKeyCommitment.instInhabited : Inhabited NullifierKeyCommitment where
  default := NullifierKeyCommitment.privateMk
