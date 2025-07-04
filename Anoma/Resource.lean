
import Prelude
import Anoma.ConsumedCreated
import Anoma.Nullifier

namespace Anoma

abbrev Nonce := Nat
abbrev CommitmentRoot := Nat

def CommitmentRoot.placeholder : CommitmentRoot := 0

/-- Representation of Anoma Resource data, without the resource logic. In the
    GOOSE model, the resource logic is determined by the `label` field (which
    contains the unique label of the class). -/
structure Resource where
  Val : SomeType
  Label : SomeType
  label : Label.type
  quantity : Nat
  value : Val.type
  ephemeral : Bool
  nonce : Nonce
  nullifierKeyCommitment : NullifierKeyCommitment

structure Logic.Args (Data : Type u) where
  self : Resource
  status : ConsumedCreated
  consumed : List Resource
  created : List Resource
  /-- `data` is the action's appData for self -/
  data : Data

def Logic.Args.isConsumed {Data : Type u} (d : Logic.Args Data) :=  d.status.isConsumed

/-- Corresponds to Anoma Resource (with resource logic). -/
structure ResourceWithLogic (Data : Type u) where
  val : Resource
  logic : Logic.Args Data → Bool

structure RootedNullifiableResource where
  key : NullifierKey
  resource : Resource
  root : CommitmentRoot

-- TODO placeholder implementation
/-- If the key matches the resource.nullifierKeyCommitment then it returns the nullifier of the resource -/
def nullify (_res : RootedNullifiableResource) : Option Nullifier := none

def RootedNullifiableResource.Transparent.fromResource (res : Resource) : RootedNullifiableResource  :=
 { key := NullifierKey.universal,
   resource := res,
   -- TODO: shouldn't we use a real commitment root?
   root := CommitmentRoot.placeholder }

inductive Commitment where
  | privateMk : Commitment
  deriving Inhabited, Repr, BEq, Hashable

/-- Computes the commitment of a Resource -/
def Resource.commitment (_r : Resource) : Commitment := Commitment.privateMk
