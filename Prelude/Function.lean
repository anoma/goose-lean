def Pi (ts : List (Type u)) (ret : Type v) : Type (max u v) :=
  match ts with
  | .nil => ULift.{u} ret
  | .cons x xs => x → Pi xs ret
