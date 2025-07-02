
universe u v w z

variable {A : Type u} {B : Type v} {C : Type w} {D : Type z}

def List.zipWithExact (f : A → B → C) (l1 : List A) (l2 : List B) : List C :=
  match l1, l2 with
  | [], [] => []
  | a :: as, b :: bs => f a b :: List.zipWithExact f as bs
  | _, _ => panic! "List.zipWithExact: lists must have the same length"

def List.zipWith3Exact (f : A → B → C → D) (l1 : List A) (l2 : List B) (l3 : List C) : List D :=
  match l1, l2, l3 with
  | [], [], [] => []
  | a :: as, b :: bs, c :: cs => f a b c :: List.zipWith3Exact f as bs cs
  | _, _, _ => panic! "List.zipWith3Exact: lists must have the same length"
