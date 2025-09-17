import Prelude.HBeq
import Mathlib.Data.Vector.Defs
import Init.Data.List.Basic
import Mathlib.Logic.Lemmas

namespace List.Vector

instance instBEq {n : Nat} {α : Type u} [BEq α] : BEq (Vector α n) where
  beq a b := a.toList == b.toList

instance instHBEq {n m : Nat} {α : Type u} [BEq α] : HBEq (Vector α n) (Vector α m) where
  hbeq v u := v.toList == u.toList

instance instReflHBEq {n : Nat} {α : Type u} [BEq α] [ReflBEq α] : ReflHBEq (Vector α n) where
  rfl := by intro v; unfold HBEq.hbeq instHBEq BEq.beq; apply List.instReflBEq.rfl

instance instLawfulHBeq
  {n m : Nat}
  {α : Type u}
  [BEq α]
  [LawfulBEq α]
  : LawfulHBEq (Vector α n) (Vector α m) where
  heq_of_hbeq := by
    intro a b heq
    unfold HBEq.hbeq instHBEq at heq
    simp at heq
    have h : n = m := by
      calc n = a.toList.length := (toList_length a).symm
           _ = b.toList.length := congrArg List.length heq
           _ = m := toList_length b
    subst h
    exact heq_of_eq (List.Vector.eq _ _ heq)

def singleton {α : Type u} (a : α) : Vector α 1 := Vector.ofFn (fun 0 => a)

def uncons {α : Type u} {n : Nat} (v : Vector α n.succ) : α × Vector α n := ⟨v.head, v.tail⟩

def split {α : Type u} {m n : Nat} (v : Vector α (m + n)) : Vector α m × Vector α n :=
  match n with
  | 0 => ⟨v, Vector.nil⟩
  | .succ l =>
    let ⟨h, t⟩ := v.uncons
    let ⟨x, y⟩ := split (n := l) t
    ⟨x, .cons h y⟩
