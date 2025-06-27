
import Lean

abbrev Rep : Type := String

class TypeRep (A : Type) where
  /-- A unique representation of the type – can be a unique type name. -/
  rep : Rep

/-- Derives a TypeRep instance for a given type which uses the type name as the
  unique type representation. -/
macro "derive_type_rep " n:ident : command => do
  let inst ← `(instance : TypeRep $n where
    rep := $(Lean.Quote.quote (n.getId.toStringWithSep "." false)))
  pure inst

private axiom uniqueTypeRep (A B : Type) [TypeRep A] [TypeRep B] : TypeRep.rep A = TypeRep.rep B → A = B

/-- Casting based on equality of type representations. -/
def rcast {A B : Type} [TypeRep A] [TypeRep B] (h : TypeRep.rep A = TypeRep.rep B) (x : A) : B :=
  cast (uniqueTypeRep A B h) x
