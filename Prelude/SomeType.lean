
import Prelude.TypeRep

structure SomeType : Type (u + 1) where
  type : Type u
  [typeTypeRep : TypeRep type]
  [typeBEq : BEq type]

instance SomeType.hasTypeRep : TypeRep SomeType where
  rep := Rep.atomic "SomeType"

instance SomeType.hasBEq : BEq SomeType where
  beq a b := a.typeTypeRep.rep == b.typeTypeRep.rep

instance SomeType.instReflBEq : ReflBEq SomeType where
  rfl := by intro; unfold BEq.beq hasBEq; simp

instance {A : SomeType} : TypeRep A.type := A.typeTypeRep

instance {A : SomeType} : BEq A.type := A.typeBEq

def SomeType.cast {A B : SomeType} (a : A.type) : Option B.type :=
  tryCast (repA := A.typeTypeRep) (repB := B.typeTypeRep) a

instance : CoeHead SomeType Type where
  coe (ty : SomeType) := ty.type
