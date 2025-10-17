import Prelude
import Anoma.Resource
import Anoma.Logic
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

structure Program.ResourceQuery where
  uid : ObjectId

inductive Program.Error : Type where
  | identityError (msg : String)
  | storageError (msg : String)
  | logicFailed
  | missingLogic (ref : LogicRef)
  | balanceCheck (msg : String)
  | typeError (msg : String)
  | userError
  deriving Repr

/-- Represents an Anoma program, as per
  https://forum.anoma.net/t/reifying-the-local-domain-solver-and-controller-in-the-avm
  -/
inductive Program where
  | skip
  | raise (err : Program.Error)
  | tryCatch (prog : Program) (onError : Program.Error → Program) (next : Program)
  | withRandomGen (next : StdGen → Program)
  | queryResource (query : Program.ResourceQuery) (next : Resource → Program)
  | submitTransaction (tx : Transaction) (next : Program)
  | log (msg : String) (next : Program)
  -- | decrypt (engine : EngineId) (data : Ciphertext) (next : Plaintext → Program)
  -- | requestCommitment (engine : EngineId) (data : Signable) (next : Commitment → Program)
  -- | generateIdentity (backend : Backend) (params : IDParams) (capabilities : Capabilities)
  --     (next : (commitmentEngine : Option EngineId) → (decryptionEngine : Option EngineId) → (externalIdentity : EngineId) → Program)
  -- | connectIdentity (externalIdentity : EngineId) (backend : Backend) (capabilities : Capabilities)
  --     (next : (commitmentEngine : Option EngineId) → (decryptionEngine : Option EngineId) → Program)
  -- | deleteIdentity (externalIdentity : EngineId) (backend : Backend) (next : Program)
  -- | getValue (key : StorageKey) (next : Option StorageValue → Program)
  -- | setValue (key : StorageKey) (value : StorageValue) (next : Program)
  -- | deleteValue (key : StorageKey) (next : Program)

def Program.genObjectId (next : ObjectId → Program) : Program :=
  Program.withRandomGen fun g =>
    let objId := stdNext g |>.fst
    next objId

def Program.withRand (prog : Rand Program) : Program :=
  Program.withRandomGen fun g =>
    prog.run' (ULift.up g)

def Program.withRandOption (prog : Rand (Option Program)) : Program :=
  Program.withRandomGen fun g =>
    let next? := prog.run' (ULift.up g)
    match next? with
    | none => Program.raise Program.Error.userError
    | some next => next
