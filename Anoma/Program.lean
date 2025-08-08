import Prelude
import Anoma.Resource
import Anoma.Transaction
import Anoma.Identities

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

inductive Program where
  | skip
  | raise (err : Program.Error)
  | tryCatch (prog : Program) (onError : Program.Error → Program) (next : Program)
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
