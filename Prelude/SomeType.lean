
import Prelude.TypeRep

structure SomeType where
  type : Type
  [rep : TypeRep type]
  [beq : BEq type]

instance SomeType.hasTypeRep : TypeRep SomeType where
  rep := Rep.atomic "SomeType"

instance SomeType.hasBEq : BEq SomeType where
  beq a b := a.rep.rep == b.rep.rep

def SomeType.equal {A B : SomeType} (a : A.type) (b : B.type) : Bool :=
  beqCast (repA := A.rep) (repB := B.rep) (beqB := B.beq) a b
