
import Prelude.TypeRep

structure SomeType : Type (u + 1) where
  type : Type u
  [typeTypeRep : TypeRep type]
  [typeBEq : BEq type]
  [typeHashable : Hashable type]

instance SomeType.hasTypeRep : TypeRep SomeType where
  rep := Rep.atomic "SomeType"

instance SomeType.hasBEq : BEq SomeType where
  beq a b := a.typeTypeRep.rep == b.typeTypeRep.rep

instance SomeType.instReflBEq : ReflBEq SomeType where
  rfl := by intro; unfold BEq.beq hasBEq; simp

private axiom SomeType.eqTypeRep.{u} {A B : SomeType.{u}} : A.typeTypeRep.rep = B.typeTypeRep.rep → A = B

instance SomeType.instLawfulBEq : LawfulBEq SomeType where
  eq_of_beq := by
    intro a b eq
    simp [BEq.beq] at eq
    exact SomeType.eqTypeRep eq

instance {A : SomeType} : TypeRep A.type := A.typeTypeRep

instance {A : SomeType} : BEq A.type := A.typeBEq

def SomeType.cast {A B : SomeType} (a : A.type) : Option B.type :=
  tryCast (repA := A.typeTypeRep) (repB := B.typeTypeRep) a

instance : CoeHead SomeType Type where
  coe (ty : SomeType) := ty.type
