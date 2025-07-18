import Mathlib.Data.FinEnum

namespace FinEnum

def decImage {A : Type u} [FinEnum A] {B : (a : A) → Type v} {P : {a : A} → B a → Prop}
  (f : (a : A) → B a)
  (dec : {a : A} → (b : B a) → Decidable (P b))
  : (∀ a : A, PLift (P (f a))) ⊕ (Σ a : A, PLift (¬ (P (f a)))) := sorry

def decImageOption {A : Type u} [FinEnum A] {B : (a : A) → Type v}
  (f : (a : A) -> Option (B a))
  : (∀ a : A, PLift ((f a).isSome)) ⊕ (Σ a : A, PLift (¬ (f a).isSome)) :=
  let IsSomeDec {a : A} (m : Option (B a)) : Decidable m.isSome :=
      match m with
      | none => isFalse (fun _ => by contradiction)
      | some _ => isTrue rfl
  decImage f IsSomeDec

end FinEnum
