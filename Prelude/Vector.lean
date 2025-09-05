import Prelude.HBeq
import Init.Data.Vector.DecidableEq
import Mathlib.Logic.Lemmas

namespace Vector

instance instHBeq {n m : Nat} {α : Type u} [BEq α] : HBeq (Vector α n) (Vector α m) where
  hbeq v u :=
    if h : n = m then v == h ▸ u
    else false

instance instReflHBeq {n : Nat} {α : Type u} [BEq α] [ReflBEq α] : ReflHBeq (Vector α n) where
  rfl := by intro; unfold HBeq.hbeq instHBeq; simp

instance instLawfulHBeq
  {n m : Nat}
  {α : Type u}
  [BEq α]
  [LawfulBEq α]
  : LawfulHBeq (Vector α n) (Vector α m) where
  heq_of_hbeq := by
    intro a b heq
    unfold HBeq.hbeq instHBeq at heq
    simp at heq
    split at heq
    grind
    contradiction
