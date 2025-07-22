import Mathlib.Data.FinEnum
import Prelude.FinEnum.Derive
import Prelude.TypeRep

/-- Universe polymorphic unit type -/
inductive UUnit : Type u where
  | unit : UUnit
deriving Repr, BEq, Inhabited

instance : TypeRep UUnit where
  rep := Rep.atomic "UUnit"

instance UUnit.instDecidableEq : DecidableEq UUnit.{0} :=
  fun .unit .unit => isTrue rfl

#FinEnum.derive UUnit
