import Prelude
import Anoma.ConsumedCreated
import Anoma.Nullifier
import Anoma.Nonce
import Anoma.Identities

namespace Anoma

structure LogicRef where
  ref : String
  deriving BEq, Repr, Inhabited, Hashable

/-- Representation of Anoma Resource data. -/
structure Resource.{u, v} : Type (max u v + 1) where
  Label : SomeType.{v}
  label : Label.type
  Val : SomeType.{u}
  value : Val.type
  logicRef : LogicRef
  quantity : Nat
  ephemeral : Bool
  nonce : Nonce
  nullifierKeyCommitment : NullifierKeyCommitment

namespace Resource

instance instHashable : Hashable Resource where
  hash r :=
    Hashable.Mix.run do
      have := r.Label.typeHashable
      have := r.Val.typeHashable
      mix r.value
      mix r.label
      mix r.logicRef
      mix r.logicRef
      mix r.quantity
      mix r.ephemeral
      mix r.nonce
      mix r.nullifierKeyCommitment

structure Kind.{v} : Type (v + 1) where
  Label : SomeType.{v}
  label : Label.type
  logicRef : LogicRef

def kind (r : Resource) : Kind where
  Label := r.Label
  label := r.label
  logicRef := r.logicRef

namespace Kind

  instance instBEq : BEq Kind where
    beq a b := a.label === b.label
      && a.logicRef == b.logicRef

  instance instHashable : Hashable Kind where
    hash a := Hashable.Mix.run do
      have := a.Label.typeHashable
      mix a.label
      mix a.logicRef

end Kind

instance instBEq : BEq Resource where
  beq a b := a.label === b.label
    && a.logicRef == b.logicRef
    && a.quantity == b.quantity
    && a.value === b.value
    && a.ephemeral === b.ephemeral
    && a.nonce === b.nonce
    && a.nullifierKeyCommitment === b.nullifierKeyCommitment

def isEphemeral (r : Resource) : Bool :=
  r.ephemeral

def isPersistent (r : Resource) : Bool :=
  not r.isEphemeral

end Resource

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

/-- Computes the commitment of a Resource (mock implementation). -/
def Resource.commitment (r : Resource) : Commitment :=
  Signature.ed25519Signature s!"{hash r}"
