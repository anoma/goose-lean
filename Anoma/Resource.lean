
import Prelude
import Anoma.ConsumedCreated
import Anoma.Nullifier
import Anoma.Nonce

namespace Anoma

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

/-- A proof that `key` can nullify the resources `res` -/
structure CanNullifyResource (key : NullifierKey) (res : Resource) : Prop where
  proof : NullifierKeyMatchesCommitment key res.nullifierKeyCommitment

/-- Cast from CanNullifyResource to a Nullifier. This is a no-op -/
def CanNullifyResource.nullifier {key : NullifierKey} {res : Resource} (_proof : CanNullifyResource key res) : Nullifier := Nullifier.privateMk

-- TODO placeholder implementation
/-- If the key matches the resource.nullifierKeyCommitment then it returns the nullifier of the resource -/
def nullify (key : Anoma.NullifierKey) (res : Resource) : Decidable (CanNullifyResource key res) :=
  match checkNullifierKey key res.nullifierKeyCommitment with
  | isTrue p => isTrue (by constructor; exact p)
  | isFalse n => isFalse (by intro h; cases h; contradiction)

def nullifyUniversal (res : Resource) (key : Anoma.NullifierKey)
  (p1 : key = .universal)
  (p2 : res.nullifierKeyCommitment = .universal)
  : CanNullifyResource key res
  := by
  constructor
  rw [p1, p2]
  constructor

inductive Commitment where
  | privateMk : Commitment
  deriving Inhabited, Repr, BEq, Hashable

/-- Computes the commitment of a Resource -/
def Resource.commitment (_r : Resource) : Commitment := Commitment.privateMk
