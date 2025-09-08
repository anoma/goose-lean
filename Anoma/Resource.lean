import Prelude
import Anoma.ConsumedCreated
import Anoma.Nullifier
import Anoma.Nonce
import Anoma.Identities

namespace Anoma

structure LogicRef where
  ref : String
  deriving BEq, Repr, Inhabited

/-- Representation of Anoma Resource data. -/
structure Resource.{u, v} : Type (max u v + 1) where
  Val : SomeType.{u}
  Label : SomeType.{v}
  label : Label.type
  logicRef : LogicRef
  quantity : Nat
  value : Val.type
  ephemeral : Bool
  nonce : Nonce
  nullifierKeyCommitment : NullifierKeyCommitment

instance Resource.instBEq : BEq Resource where
  beq a b := a.label === b.label
    && a.logicRef == b.logicRef
    && a.quantity == b.quantity
    && a.value === b.value
    && a.ephemeral === b.ephemeral
    && a.nonce === b.nonce
    && a.nullifierKeyCommitment === b.nullifierKeyCommitment

def Resource.isEphemeral (r : Resource) : Bool :=
  r.ephemeral

def Resource.isPersistent (r : Resource) : Bool :=
  not r.isEphemeral

/-- A proof that `key` can nullify the resources `res` -/
structure CanNullifyResource (key : NullifierKey) (res : Resource) : Prop where
  proof : NullifierKeyMatchesCommitment key res.nullifierKeyCommitment

/-- Cast from CanNullifyResource to a Nullifier. This is a no-op -/
def CanNullifyResource.nullifier {key : NullifierKey} {res : Resource} (_proof : CanNullifyResource key res) : Nullifier := Nullifier.privateMk

-- TODO placeholder implementation
/-- If the key matches the resource.nullifierKeyCommitment then it returns the nullifier of the resource -/
def Resource.nullify (key : Anoma.NullifierKey) (res : Resource) : Decidable (CanNullifyResource key res) :=
  match checkNullifierKey key res.nullifierKeyCommitment with
  | isTrue p => isTrue (by constructor; exact p)
  | isFalse n => isFalse (by intro h; cases h; contradiction)

def Resource.nullifyUniversal (res : Resource)
  (p1 : res.nullifierKeyCommitment = .universal := by rfl)
  : CanNullifyResource .universal res
  := by
  constructor
  rw [p1]
  constructor

/-- Computes the commitment of a Resource -/
def Resource.commitment (_r : Resource) : Commitment :=
  -- TODO: Replace with proper serialization and hashing of all relevant fields
  Signature.ed25519Signature "dummy"
