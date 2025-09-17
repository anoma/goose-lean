def Pi (ts : List (Type u)) (α : Type v) : Type (max u v) :=
  match ts with
  | .nil => ULift.{u} α
  | .cons x xs => x → Pi xs α
