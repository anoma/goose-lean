
import Anoma.Raw

namespace Anoma

abbrev Nonce := Nat
abbrev CommitmentRoot := Nat
abbrev NullifierKeyCommitment := String
abbrev NullifierKey := String

structure Resource where
  Val : Type u
  [rawVal : Raw Val]
  label : String
  quantity : Nat
  value : Val
  ephemeral : Bool
  nonce : Nonce
  nullifierKeyCommitment : NullifierKeyCommitment

structure Logic.Args (Data : Type u) where
  self : Resource
  isConsumed : Bool
  consumed : List Resource
  created : List Resource
  -- data is the action's appData for self
  data : Data

structure RootedNullifiableResource where
  key : NullifierKey
  resource : Resource
  root : CommitmentRoot

structure ResourceWithLogic (Data : Type u) where
  val : Resource
  logic : Logic.Args Data

def Resource.commitment (res : Resource) : String :=
  -- whatever
  res.label ++ "-" ++ toString res.nonce

def Resource.nullifier (res : Resource) : String :=
  -- whatever
  res.label ++ "-" ++ toString res.nonce

end Anoma
