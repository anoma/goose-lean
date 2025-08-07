import Mathlib.Data.FinEnum

namespace FinEnum

def decImageFin {c : Nat} {B : (a : Fin c) → Type v} {P : {a : Fin c} → B a → Prop}
  (f : (a : Fin c) → B a)
  (dec : {a : Fin c} → (b : B a) → Decidable (P b))
  : (∀ a : Fin c, PLift (P (f a))) ⊕ (Σ a : Fin c, PLift (¬ (P (f a)))) := by
  induction c; constructor; intro a
  cases a; contradiction
  next n ih =>
    cases dec (f (Fin.last n))
    next neg => exact Sum.inr ⟨_, ⟨neg⟩⟩
    next pos =>
      cases @ih _ _ (fun x => f x.castSucc) (fun x => dec x)
      next ih_pos =>
        left; intro fa; have ⟨a, pa⟩ := fa
        if h1 : a < n
        then constructor; exact (ih_pos ⟨a, h1⟩).down
        else
          constructor; have e : a = n := by omega
          have eq : ⟨a, pa⟩ = Fin.last n := Fin.ext_iff.mpr e
          rw [eq]; assumption
      next ih_neg =>
        have ⟨x, px⟩ := ih_neg
        exact Sum.inr ⟨x.castSucc, px⟩

def decImage {A : Type u} [enum : FinEnum A] {B : (a : A) → Type v} {P : {a : A} → B a → Prop}
  (f : (a : A) → B a)
  (dec : {a : A} → (b : B a) → Decidable (P b))
  : (∀ a : A, PLift (P (f a))) ⊕ (Σ a : A, PLift (¬ (P (f a)))) :=
  let inv := enum.equiv.invFun
  let toFun := enum.equiv.toFun
  let c := enum.card
  let B' (a : Fin c) : Type v := B (inv a)
  let P' {a : Fin c} (b : B' a) : Prop := P b
  let f' (a : Fin c) : B' a := f (inv a)
  let dec' {a : Fin c} (b : B' a) : Decidable (P' b) := dec b
  match decImageFin f' dec' with
  | .inl p => by
    left; intro a; constructor
    rw [← enum.equiv.left_inv a]; exact (p (toFun a)).down
  | .inr ⟨n, ⟨p⟩⟩ => by right; refine ⟨inv n, ?_⟩; constructor; intro; contradiction

def IsSomeDec {a : A} {B : (a : A) → Type u} (m : Option (B a)) : Decidable m.isSome :=
  match m with
  | none => isFalse (fun _ => by contradiction)
  | some _ => isTrue rfl

def decImageOption {A : Type u} [FinEnum A] {B : (a : A) → Type v}
  (f : (a : A) -> Option (B a))
  : (∀ a : A, PLift ((f a).isSome)) ⊕ (Σ a : A, PLift (¬ (f a).isSome)) :=
  decImage f IsSomeDec

def decImageOption' {A : Type u} [enum : FinEnum A] {B : (a : A) → Type v}
  (f : (a : A) -> Option (B a))
  : Option (∀ a : A, B a) :=
  match decImage f IsSomeDec with
  | .inr _ => none
  | .inl p => some <| fun a =>
    match p1 : f a with
    | some b => b
    | none => by
        have c := (p a).down
        rw [p1] at c
        contradiction

instance extBEq {T : Type} (A : T → Type u) [enum : FinEnum T] [instBEq : (t : T) → BEq (A t)]
  : BEq ((t : T) → A t) where
  beq f g :=
    let rec go (args : List T) : Bool :=
        match args with
        | [] => true
        | a :: as => f a == g a && go as
    go enum.toList

def toVector {T : Type u} [enum : FinEnum T] : Vector T enum.card :=
  Vector.finRange enum.card
  |>.map enum.equiv.symm
