/- Types for network identities, following
  https://specs.anoma.net/main/arch/node/types/identities.html. -/

import Prelude
import Anoma.Crypto

namespace Anoma

/-- Unique object identifier. -/
abbrev ObjectId := Nat

/-- Encrypted data. -/
abbrev Ciphertext := ByteArray

/-- Raw unencrypted data. -/
abbrev Plaintext := String

/-- A type representing data that can be cryptographically signed. -/
abbrev Signable := String

/-- A unique identifier, such as a public key, represented as a natural number. -/
abbrev ExternalId := PublicKey

/-- A unique identifier, such as a private key, used internally within the network. -/
abbrev InternalId := PrivateKey

/-- A pair combining an ExternalID and an InternalID. -/
abbrev Identity := ExternalId × InternalId

/-- A cryptographic signature or commitment. -/
abbrev Commitment := Signature

/-- Cryptographic node identity. -/
abbrev NodeId := ExternalId

/-- Engine instance name as an opaque string. -/
abbrev EngineName := String
abbrev ExternalIdentity := EngineName

/-- Engine instance identity combining node identity and engine name. -/
abbrev EngineId := Option NodeId × EngineName

def isLocalEngineID (eid : EngineId) : Bool :=
  match eid with
  | (none, _) => true
  | _ => false

def isRemoteEngineID (eid : EngineId) : Bool := not (isLocalEngineID eid)

/-- Supported identity parameter types. -/
inductive IDParams where
  | Ed25519
  | Secp256k1
  | BLS

/-- Backend connection types. -/
inductive Backend where
  | localMemory
  | localConnection (subtype : String)
  | remoteConnection (externalIdentity : ExternalIdentity)

/-- Available identity capabilities. -/
inductive Capabilities where
  | commit
  | decrypt
  | commitAndDecrypt
