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
structure Resource : Type 2 where
  Label : SomeType.{1}
  label : Label.type
  Val : SomeType.{1}
  value : Val.type
  logicRef : LogicRef
  quantity : Nat
  ephemeral : Bool
  nonce : Nonce
  nullifierKeyCommitment : NullifierKeyCommitment

namespace Resource

def h (x : Lean.Json) : String := toString x

instance instRepr : Repr Resource where
  reprPrec r _ :=
    have := r.Label.typeRepr
    have := r.Val.typeRepr
    s!"Resource@\{
      label := {repr r.label}
      value := {repr r.value}
      logicRef := {repr r.logicRef}
      quantity := {repr r.quantity}
      ephemeral := {repr r.ephemeral}
      nonce := {repr r.nonce}
    }"

instance instHashable : Hashable Resource where
  hash r :=
    Hashable.Mix.run do
      have := r.Label.typeHashable
      have := r.Val.typeHashable
      mix r.value
      mix r.label
      mix r.logicRef
      mix r.quantity
      mix r.ephemeral
      mix r.nonce
      mix r.nullifierKeyCommitment

structure Kind : Type 2 where
  Label : SomeType.{1}
  label : Label.type
  logicRef : LogicRef

instance Kind.instRepr : Repr Kind where
  reprPrec k _ :=
    have := k.Label.typeRepr
    s!"Kind@\{
      label := {repr k.label}
      logicRef:= {repr k.logicRef}
    }"

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
