
import Prelude
import Anoma.NullifierKey
import Anoma.Nonce

namespace Anoma

/-- A public value derived from a secret NullifierKey and a Resource -/
inductive Nullifier where
  | privateMk : Nullifier
  deriving Repr, BEq, Hashable

instance : TypeRep NullifierKeyCommitment where
  rep := Rep.atomic "NullifierKeyCommitment"

def Nullifier.toNonce (_nullif : Nullifier) : Nonce :=
  -- TODO: Implement a proper conversion from Nullifier to Nonce to avoid collisions.
  -- For now, this is a placeholder implementation that always returns 0.
  0
