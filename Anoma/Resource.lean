
import Anoma.Raw

namespace Anoma

abbrev Nonce := Nat
abbrev NullifierKeyCommitment := String

structure Resource where
  Val : Type
  [rawVal : Raw Val]
  label : String
  quantity : Nat
  value : Val
  ephemeral : Bool
  nonce : Nonce
  nullifierKeyCommitment : NullifierKeyCommitment

structure Logic.Args (Data : Type) where
  self : Resource
  isConsumed : Bool
  consumed : List Resource
  created : List Resource
  data : Data

structure ResourceWithLogic (Data : Type) where
  val : Resource
  logic : Logic.Args Data

def Resource.commitment (res : Resource) : String :=
  -- whatever
  res.label ++ "-" ++ toString res.nonce

def Resource.nullifier (res : Resource) : String :=
  -- whatever
  res.label ++ "-" ++ toString res.nonce

end Anoma
