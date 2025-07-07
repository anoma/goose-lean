
import Prelude.TypeRep

structure SomeType where
  type : Type u
  [instTypeRep : TypeRep type]
  [instBEq : BEq type]

instance SomeType.hasTypeRep : TypeRep SomeType where
  rep := Rep.atomic "SomeType"

instance SomeType.hasBEq : BEq SomeType where
  beq a b := a.instTypeRep.rep == b.instTypeRep.rep

instance {A : SomeType} : TypeRep A.type where
  rep := A.instTypeRep.rep

instance {A : SomeType} : BEq A.type where
  beq := A.instBEq.beq

def SomeType.cast {A B : SomeType} (a : A.type) : Option B.type :=
  tryCast (repA := A.instTypeRep) (repB := B.instTypeRep) a

instance : CoeHead SomeType Type where
  coe (ty : SomeType) := ty.type
