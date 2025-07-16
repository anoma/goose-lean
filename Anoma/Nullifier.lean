
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
  -- Placeholder implementation
  0
