
import Lean
import Prelude.List

mutual
  inductive Rep where
    /-- `Rep.atomic` is used for types without parameters (these can be uniquely
      identified by the type name) -/
    | atomic (name : String)
    /-- `Rep.composite` is used for parameterised data types -/
    | composite (name : String) (constrs : List Constr.Rep)
  deriving Inhabited, Repr, BEq

  structure Constr.Rep where
    /-- The name of the constructor. -/
    name : String
    /-- The arguments of the constructor. -/
    args : List Rep
  deriving Inhabited, Repr, BEq
end

mutual
  partial def Rep.decEq (a b : Rep) : Decidable (Eq a b) :=
    match a with
    | Rep.atomic nameA =>
      match b with
      | Rep.atomic nameB =>
        if h : nameA = nameB then
          isTrue (by rw [h])
        else
          isFalse (fun heq => by cases heq; contradiction)
      | Rep.composite _ _ =>
        isFalse (fun h => by injection h)
    | Rep.composite nameA constrsA =>
      match b with
      | Rep.atomic _ =>
        isFalse (fun h => by injection h)
      | Rep.composite nameB constrsB =>
        if h : nameA = nameB then
          let constrsDecEq : Decidable (constrsA = constrsB) := @List.hasDecEq _ Constr.Rep.decEq constrsA constrsB
          match constrsDecEq with
          | isTrue heq =>
            isTrue (by rw [heq, h])
          | isFalse hne =>
            isFalse (fun heq => by cases heq; contradiction)
        else
          isFalse (fun h => by cases h; contradiction)

  partial def Constr.Rep.decEq (a b : Constr.Rep) : Decidable (Eq a b) :=
    match a, b with
    | { name := nameA, args := argsA }, { name := nameB, args := argsB } =>
      if h : nameA = nameB then
        let argsDecEq : Decidable (argsA = argsB) := @List.hasDecEq _ Rep.decEq argsA argsB
        match argsDecEq with
        | isTrue heq =>
          isTrue (by rw [heq, h])
        | isFalse hne =>
          isFalse (fun heq => by cases heq; contradiction)
      else
        isFalse (fun h => by cases h; contradiction)
end

instance Rep.hasDecEq : DecidableEq Rep := Rep.decEq
instance Constr.Rep.hasDecEq : DecidableEq Constr.Rep := Constr.Rep.decEq

class TypeRep (A : Type) where
  /-- A unique representation of the type. -/
  rep : Rep

/-- Derives a TypeRep instance for a given type. -/
-- TODO: this should derive a generic instance for parameterised types (e.g.
-- TypeRep A => TypeRep (List A)), currently just uses unique type name (e.g.
-- List).
macro "derive_type_rep " n:ident : command => do
  let inst ← `(instance : TypeRep $n where
    rep := Rep.atomic $(Lean.Quote.quote (n.getId.toStringWithSep "." false)))
  pure inst

private axiom uniqueTypeRep (A B : Type) [TypeRep A] [TypeRep B] : TypeRep.rep A = TypeRep.rep B → A = B

/-- Casting based on equality of type representations. -/
def rcast {A B : Type} [TypeRep A] [TypeRep B] (h : TypeRep.rep A = TypeRep.rep B) (x : A) : B :=
  cast (uniqueTypeRep A B h) x

derive_type_rep Nat
derive_type_rep String

-- Examples:
-- #eval (inferInstance : TypeRep Nat).rep
-- #eval (inferInstance : TypeRep String).rep
