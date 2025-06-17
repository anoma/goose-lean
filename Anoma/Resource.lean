
namespace Anoma

abbrev Nonce := Nat
abbrev NullifierKeyCommitment := String

structure Resource where
  Args : Type
  Val : Type
  logic : Args → Bool
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

end Anoma
