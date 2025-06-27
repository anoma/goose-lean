
import Lean
open Lean Meta Elab Command

abbrev Rep : Type := String

class TypeRep (A : Type) where
  /-- A unique representation of the type – can be a unique type name. -/
  rep : Rep

macro "derive_type_rep " n:ident : command => do
  let inst ← `(instance : TypeRep $n where
    rep := $(Quote.quote n.getId.getString!))
  pure inst

axiom uniqueTypeRep (A B : Type) [TypeRep A] [TypeRep B] : TypeRep.rep A = TypeRep.rep B → A = B

def rcast {A B : Type} [TypeRep A] [TypeRep B] (h : TypeRep.rep A = TypeRep.rep B) (x : A) : B :=
  cast (uniqueTypeRep A B h) x
