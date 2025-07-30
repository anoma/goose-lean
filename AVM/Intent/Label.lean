
import Prelude

namespace AVM

structure Intent.Label where
  /-- The type of intent arguments. The arguments are stored in the `label`
    field of the intent resource (see `Intent.ResourceData` in
    `AVM/Intent.lean`). The intent arguments are not provided in the
    app data for any resource logics. -/
  Args : SomeType
  /-- The unique name of the intent. -/
  name : String
  deriving BEq

namespace Intent.Label

instance instReflBEq : ReflBEq Label where
  rfl := by intro; unfold BEq.beq instBEqLabel; simp!

instance instLawfulBEq : LawfulBEq Label where
  eq_of_beq := by
    intro a b eq
    cases a; cases b; simp
    unfold BEq.beq instBEqLabel at eq; simp! at eq; cases eq;
    constructor <;> assumption

instance hasTypeRep : TypeRep Intent.Label where
  rep := Rep.atomic "AVM.Intent.Label"

instance hasHashable : Hashable Intent.Label where
  hash a := hash a.name
