import Mathlib.Data.FinEnum

import Prelude.TypeRep

/-- Universe polymorphic unit type -/
inductive UUnit : Type u where
  | unit : UUnit
deriving Repr, BEq, Inhabited

instance : TypeRep UUnit where
  rep := Rep.atomic "UUnit"

instance UUnit.instDecidableEq : DecidableEq UUnit.{0} :=
  fun .unit .unit => isTrue rfl

instance UUnit.instFinEnum : FinEnum UUnit where
  card := 1
  equiv : UUnit ≃ Fin 1 :=
    { toFun := fun _ => 0
      invFun := fun _ => UUnit.unit
      right_inv := fun x =>
        match x with
        | 0 => rfl
      left_inv := fun x =>
        match x with
        | UUnit.unit => rfl }
