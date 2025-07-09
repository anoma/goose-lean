
import Prelude.TypeRep

/-- Universe polymorphic unit type -/
inductive UUnit : Type u where
  | unit : UUnit
deriving Repr, BEq, Inhabited

instance : TypeRep UUnit where
  rep := Rep.atomic "UUnit"
