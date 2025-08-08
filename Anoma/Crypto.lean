/- Cryptographic primitives, following
  https://specs.anoma.net/main/arch/node/types/crypto.html. -/

import Prelude

namespace Anoma

/-- Public key for public-key cryptography. -/
inductive PublicKey where
  | curve25519PubKey (key : String)
  deriving Inhabited, Repr, BEq, Hashable

/-- Private key for public-key cryptography. -/
inductive PrivateKey where
  | curve25519PrivKey (key : String)
  deriving Inhabited, Repr, BEq, Hashable

/-- Cryptographic signature. -/
inductive Signature where
  | ed25519Signature (sig : String)
  deriving Inhabited, Repr, BEq, Hashable

/-- Message digest. Output of a cryptographic hash function. -/
inductive Digest where
  | Blake3Digest (digest : String)
  deriving Inhabited, Repr, BEq, Hashable
