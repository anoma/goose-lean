import Prelude.LetTry
import Mathlib.Data.Prod.TProd

universe u v w z

variable {A : Type u} {B : Type v} {C : Type w} {D : Type z}

namespace List

def zipWithExactOption (f : A → B → C) (l1 : List A) (l2 : List B) : Option (List C) :=
  match l1, l2 with
  | [], [] => pure []
  | a :: as, b :: bs => do
    let t <- List.zipWithExactOption f as bs
    pure (f a b :: t)
  | _, _ => none

def zipWithExact (f : A → B → C) (l1 : List A) (l2 : List B) : List C :=
  (zipWithExactOption f l1 l2).getD (panic! "List.zipWithExact: lists must have the same length")

def zipWith3Exact (f : A → B → C → D) (l1 : List A) (l2 : List B) (l3 : List C) : List D :=
  match l1, l2, l3 with
  | [], [], [] => []
  | a :: as, b :: bs, c :: cs => f a b c :: List.zipWith3Exact f as bs cs
  | _, _, _ => panic! "List.zipWith3Exact: lists must have the same length"

def mapSome (f : A → Option B) (l : List A) : Option (List B) :=
  match l with
  | [] => some []
  | a :: as => do
    let bs ← mapSome f as
    let b ← f a
    some (b :: bs)

def getSome (l : List.{u} (Option.{u} A)) : Option.{u} (List.{u} A) :=
  l.mapSome id

def Product (tys : List (Type u)) : Type u :=
  List.TProd id tys

def toSizedVector {n : Nat} (l : List A) : Option (Vector A n) :=
  let a : Array A := l.toArray
  if h : a.size = n
  then some ⟨a, h⟩
  else none

def splitAtExact (n : Nat) (lst : List A) : Option (Vector A n × List A) :=
  let (l, r) := List.splitAt n lst
  let try l' := l.toSizedVector
  pure (l', r)

def SplitsType (A : Type u) (lengths : List Nat) : Type u :=
  match lengths with
  | [] => PUnit
  | n :: ns => Vector A n × SplitsType A ns

def splits (lst : List A) (lengths : List Nat) : Option (SplitsType A lengths × List A) :=
  match lengths with
  | [] => some (PUnit.unit, lst)
  | n :: ns =>
  let try ⟨h, t⟩ := splitAtExact n lst
  let try ⟨hs, rem⟩ := splits t ns
  some (⟨h , hs⟩, rem)

def splitsExact (lst : List A) (lengths : List Nat) : Option (SplitsType A lengths) :=
  match splits lst lengths with
  | .some (l, []) => some l
  | _ => none
