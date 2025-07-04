
import Prelude.TypeRep

structure SomeType where
  type : Type u
  [rep : TypeRep type]
  [beq : BEq type]

instance SomeType.hasTypeRep : TypeRep SomeType where
  rep := Rep.atomic "SomeType"

instance SomeType.hasBEq : BEq SomeType where
  beq a b := a.rep.rep == b.rep.rep

instance {A : SomeType} : TypeRep A.type where
  rep := A.rep.rep

instance {A : SomeType} : BEq A.type where
  beq := A.beq.beq

def SomeType.cast {A B : SomeType} (a : A.type) : Option B.type :=
  tryCast (repA := A.rep) (repB := B.rep) a
