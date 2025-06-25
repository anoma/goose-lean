
import Anoma.Raw

namespace Anoma

abbrev Nonce := Nat
abbrev CommitmentRoot := Nat
abbrev NullifierKeyCommitment := String
abbrev NullifierKey := String

def NullifierKey.Universal : NullifierKey := "universal"

def CommitmentRoot.placeholder : CommitmentRoot := 0

/-- Representation of Anoma Resource data, without the resource logic. In the
    GOOSE model, the resource logic is determined by the `label` field (which
    contains the unique label of the class). -/
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
  /-- `data` is the action's appData for self -/
  data : Data

/-- Corresponds to Anoma Resource (with resource logic). -/
structure ResourceWithLogic (Data : Type u) where
  val : Resource
  logic : Logic.Args Data → Bool

structure RootedNullifiableResource where
  key : NullifierKey
  resource : Resource
  root : CommitmentRoot

def RootedNullifiableResource.Transparent.fromResource (res : Resource) : RootedNullifiableResource  :=
 { key := NullifierKey.Universal,
   resource := res,
   -- TODO: shouldn't we use a real commitment root?
   root := CommitmentRoot.placeholder }

def Resource.commitment (res : Resource) : String :=
  -- The exact way to compute the commitment doesn't matter for the model (for
  -- now)
  res.label ++ "-" ++ toString res.nonce

def Resource.nullifier (res : Resource) : String :=
  -- The exact way to compute the nullifier doesn't matter for the model (for
  -- now)
  res.label ++ "-" ++ toString res.nonce

end Anoma
