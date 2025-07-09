
import Prelude
import Anoma.ConsumedCreated
import Anoma.Nullifier

namespace Anoma

abbrev Nonce := Nat
abbrev CommitmentRoot := Nat

def CommitmentRoot.todo : CommitmentRoot := 0

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

instance Resource.instBEq : BEq Resource where
  beq a b := a.label === b.label
    && a.quantity == b.quantity
    && a.value === b.value
    && a.ephemeral === b.ephemeral
    && a.nonce === b.nonce
    && a.nullifierKeyCommitment === b.nullifierKeyCommitment

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
def nullify (res : RootedNullifiableResource) : Option Nullifier :=
  if checkNullifierKey res.key res.resource.nullifierKeyCommitment
  then some .privateMk
  else none

def nullifyUniversal (res : RootedNullifiableResource) (p1 : res.resource.nullifierKeyCommitment = .universal) (p2 : res.key = .universal)
  : Σ n : Nullifier, PLift (nullify res = some n)
  := by
  exists .privateMk
  unfold nullify
  unfold checkNullifierKey
  rw [p1, p2]
  simp
  constructor
  simp

inductive Commitment where
  | privateMk : Commitment
  deriving Inhabited, Repr, BEq, Hashable

/-- Computes the commitment of a Resource -/
def Resource.commitment (_r : Resource) : Commitment := Commitment.privateMk
