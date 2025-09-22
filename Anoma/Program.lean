import Prelude
import Anoma.Resource
import Anoma.Transaction
import Anoma.Identities
import Mathlib.Control.Random

namespace Anoma

abbrev StorageKey := String

inductive StorageValue where
  | str (s : String)
  | int (i : Int)
  | bool (b : Bool)
  | bytes (b : ByteArray)

inductive Program.ResourceQuery where
  | queryByObjectId (uid : ObjectId)

inductive Program.Error where
  | networkError (msg : String)
  | engineError (msg : String)
  | decryptionError (msg : String)
  | commitmentError (msg : String)
  | identityError (msg : String)
  | storageError (msg : String)
  | typeError (msg : String)
  | userError

/-- Represents an Anoma program, as per
  https://forum.anoma.net/t/reifying-the-local-domain-solver-and-controller-in-the-avm
  -/
inductive Program where
  | skip
  | raise (err : Program.Error)
  | tryCatch (prog : Program) (onError : Program.Error → Program) (next : Program)
  | withRandomGen (next : StdGen → Program × StdGen)
  | queryResource (query : Program.ResourceQuery) (next : Resource → Program)
  | submitTransaction (tx : Transaction) (next : Program)
  | decrypt (engine : EngineId) (data : Ciphertext) (next : Plaintext → Program)
  | requestCommitment (engine : EngineId) (data : Signable) (next : Commitment → Program)
  | generateIdentity (backend : Backend) (params : IDParams) (capabilities : Capabilities)
      (next : (commitmentEngine : Option EngineId) → (decryptionEngine : Option EngineId) → (externalIdentity : EngineId) → Program)
  | connectIdentity (externalIdentity : EngineId) (backend : Backend) (capabilities : Capabilities)
      (next : (commitmentEngine : Option EngineId) → (decryptionEngine : Option EngineId) → Program)
  | deleteIdentity (externalIdentity : EngineId) (backend : Backend) (next : Program)
  | getValue (key : StorageKey) (next : Option StorageValue → Program)
  | setValue (key : StorageKey) (value : StorageValue) (next : Program)
  | deleteValue (key : StorageKey) (next : Program)

def Program.genObjectId (next : ObjectId → Program) : Program :=
  Program.withRandomGen fun g =>
    let (objId, g') := stdNext g
    (next objId, g')

def Program.withRand (prog : Rand Program) : Program :=
  Program.withRandomGen fun g =>
    let (next, g') := prog.run (ULift.up g)
    (next, ULift.down g')

def Program.withRandOption (prog : Rand (Option Program)) : Program :=
  Program.withRandomGen fun g =>
    let (next?, g') := prog.run (ULift.up g)
    match next? with
    | none => (Program.raise Program.Error.userError, ULift.down g')
    | some next => (next, ULift.down g')
