namespace RM

/-
risc0_zkvm background https://docs.rs/risc0-zkvm/latest/risc0_zkvm/struct.Digest.html
> pub struct Digest(/* private fields */);
> Digest represents the results of a hashing function.
-/

class HashLike (α : Type) (τ : Type) where
  -- the generation of a new digest like (https://github.com/anoma/nspec/blob/55c77654d5a3f783704ba6ffe94d7b4ff0e57ef2/docs/arch/system/state/resource_machine/primitive_interfaces/fixed_size_type/fixed_size_type.juvix.md?plain=1#L41)
  digest : α → τ
  -- the equality on τ (https://github.com/anoma/nspec/blob/55c77654d5a3f783704ba6ffe94d7b4ff0e57ef2/docs/arch/system/state/resource_machine/primitive_interfaces/fixed_size_type/fixed_size_type.juvix.md?plain=1#L42)
  equal : τ → τ → Bool
  -- equality coincides with equality of terms -- probably this is superfluous
  precise_equality : ∀ b : τ, ∀ b' : τ, b = b' ↔ equal b b'
  -- TODO: probably want to have an axiom if we do not want hash collisions (for formal verification purposes)

class FixedSize (α : Type) (τ : Type) extends HashLike α τ where
  /-- the bitsize of all
  -/
  encoding : τ → Nat

  invertible : (∃ (r : Nat → τ), id = r ∘ encoding)

  bounded : ∃ (n : Nat), (∀ (t : τ), encoding t < n)

  -- probably we want
  contiguous : ∀ (t : τ), (encoding t > 0) → (∃ (t' : τ), encoding t' = encoding t - 1)


noncomputable
def bitsize {α τ}  (d : FixedSize α τ) : Nat := Exists.choose d.bounded
-- TODO: well, we could actually compute it based of contigous (and this has a spurious Ω(exp) factor ^_^)

-- TODO Hashes: have type classes instead of arbitrary `Type u`
def LogicRef : Type (u+1) := Type u
def LabelRef : Type (u+1) := Type u

/--
https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L28-L49
/// A resource that can be created and consumed
-/
structure Resource where
  /--
  This is the top-level reference to the logic of the resource, either
  - the "outer" logic, for the case of function privacy (FP)
  - the "actual" logic, w/o any FP guarantees
  > a succinct representation of the predicate associated with the resource
  https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L33-L34
  -/
  logicRef : LogicRef
  /--
  The `labelRef` is typically the hash of the actual label
  > specif[ication of] the fungibility domain for the resource
  https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L35-L36
  -/
  labelRef : LabelRef

/--
-/
structure Piece where
-- TODO define the corresponding piece (and move it to the high-level RM)

def kindOf (x : Resource) : LogicRef × LabelRef := ⟨x.logicRef, x.labelRef⟩


end RM
