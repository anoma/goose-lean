namespace RM

/-
Just FYI (TODO, remove for final clean up)

- risc0 is using the term `digest`; this allows to avoid confusion with the function `hash`,
which computes the digest

---

risc0_zkvm background https://docs.rs/risc0-zkvm/latest/risc0_zkvm/struct.Digest.html

> pub struct Digest(/* private fields */);
> Digest represents the results of a hashing function.

-/

/-- The `HashLike` class is a slight generalization of the FixedSize class in the Anoma specification.
-/
class HashLike (α : Type) (τ : Type) where
  -- the generation of a new digest like (https://github.com/anoma/nspec/blob/55c77654d5a3f783704ba6ffe94d7b4ff0e57ef2/docs/arch/system/state/resource_machine/primitive_interfaces/fixed_size_type/fixed_size_type.juvix.md?plain=1#L41)
  digest : α → τ
  -- the equality on τ (https://github.com/anoma/nspec/blob/55c77654d5a3f783704ba6ffe94d7b4ff0e57ef2/docs/arch/system/state/resource_machine/primitive_interfaces/fixed_size_type/fixed_size_type.juvix.md?plain=1#L42)
  equal : τ → τ → Bool
  -- equality coincides with equality of terms -- probably this is superfluous
  precise_equality : ∀ b : τ, ∀ b' : τ, b = b' ↔ equal b b'
  -- TODO: probably want to have an axiom if we do not want hash collisions (for formal verification purposes)

-- TODO: fix the fixedSize -- could not resist the pun
class FixedSize (α : Type) (τ : Type) extends HashLike α τ where
  /-- The `encoding` is an injective mapping from `τ` to an initial segment of the natural numbers.
  -/
  encoding : τ → Nat

  invertible : (∃ (r : Nat → τ), id = r ∘ encoding)

  bounded : ∃ (n : Nat), (∀ (t : τ), encoding t < n)

  -- probably we want
  contiguous : ∀ (t : τ), (encoding t > 0) → (∃ (t' : τ), encoding t' = encoding t - 1)

noncomputable
-- TODO: well, we could actually compute it based of contigous (and this has a spurious Ω(exp) factor ^_^)
def bitsize {α τ}  (d : FixedSize α τ) : Nat := Exists.choose d.bounded

-- TODO Hashes: have type classes instead of arbitrary `Type u`
-- TODO could these be just variables ?
def LogicRef : Type (u+1) := Type u
def LabelRef : Type (u+1) := Type u
def ValueRef : Type (u+1) := Type u
def Nonce : Type (u+1) := Type u
def NullifierKeyCommitment : Type (u+1) := Type u
def RandSeed : Type (u+1) := Type u

-- TODO: add the description of the "additional data"
/-- A `Resource` consists of
  - digests of the fields of a `Piece` and
  - "additional data"
/-
-/
https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L28-L49
> A resource that can be created and consumed
-/
structure Resource where
  /--
  The `logigRef` is the reference to the logic of the resource, either
  - the "outer" logic, for the case of function privacy (FP) -- a constant (the inner logic is provided by the witness)
  - the "actual" logic, w/o any FP guarantees -- could even be transparent
  -/
  logicRef : LogicRef
  /-
  > a succinct representation of the predicate associated with the resource
  https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L33-L34
  -/

  /--
  The `labelRef` is typically the digest of the actual label.
  > specif[ication of] the fungibility domain for the resource
  https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L35-L36
  -/
  labelRef : LabelRef
  /--
  The `quantity` is a natural number.
  > number representing the quantity of the resource
  https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L37-L38
  -/
  quantity : Nat
  /--
  The `valueRef` is the digest of an arbitrary value.
  > the fungible value reference of the resource
  https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L39-L40
  -/
  valueRef : ValueRef
  /--
  The `isEphemal` flag is true iff the resource is ephemeral.
  -/
  /-
  > flag that reflects the resource ephemerality
  https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L41-L42
  -/
  isEphemeral: Bool

  /--
  The `nonce` is an arbitrary value, to be chosen "fresh" to avoid clashes with resources of the same kind
  -/
  /-
  >guarantees the uniqueness of the resource computable components
  https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L43-L44
  -/
  nonce: Nonce
  /--
  The `nkCommitment` is the digest of the nullifier key (to be available when spending the resource)
  -/
  /-
  > commitment to nullifier key
  https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L45-L46
  -/
  nkCommitment : NullifierKeyCommitment
  /--
  The `randSeed` is the seed, to be used for generation of pseudo-random numbers
  -/
  /-
  > randomness seed used to derive whatever randomness needed
  https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L47-L48
  -/
  randSeed: RandSeed


structure Piece where
-- TODO: Rename the current version of Resource in Anoma.lean `Anoma.Resource` to `Piece`.
-- TODO: explain how we computer the resource from a Piece
-- TODO: how to "invent" all sorts of techincal bells and whistles (in particular seed and nullifier key commitment)

-- TODO: revise `kindOf`
def kindOf (x : Resource) : LogicRef × LabelRef := ⟨x.logicRef, x.labelRef⟩

end RM
