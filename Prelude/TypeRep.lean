
import Lean
import Prelude.List

open Lean Elab Command Meta

inductive Rep where
  /-- `Rep.atomic` is used for types without parameters (these can be uniquely
    identified by the type name) or parameter values (stored in the name). -/
  | atomic (name : String)
  /-- `Rep.composite` is used for parameterised data types -/
  | composite (name : String) (params : List Rep)
deriving Inhabited, Repr, BEq

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
  | Rep.composite nameA paramsA =>
    match b with
    | Rep.atomic _ =>
      isFalse (fun h => by injection h)
    | Rep.composite nameB paramsB =>
      if h : nameA = nameB then
        let paramsDecEq : Decidable (paramsA = paramsB) := @List.hasDecEq _ Rep.decEq paramsA paramsB
        match paramsDecEq with
        | isTrue heq =>
          isTrue (by rw [heq, h])
        | isFalse hne =>
          isFalse (fun heq => by cases heq; contradiction)
      else
        isFalse (fun h => by cases h; contradiction)

instance Rep.hasDecEq : DecidableEq Rep := Rep.decEq

class TypeRep (A : Type u) where
  /-- A unique representation of the type. -/
  rep : Rep

private axiom uniqueTypeRep (A : Type u) (B : Type w) [TypeRep A] [TypeRep B] :
  TypeRep.rep A = TypeRep.rep B → ULift.{max u w} A = ULift.{max u w} B

/-- Casting based on equality of type representations. -/
def rcast {A : Type u} {B : Type w} [TypeRep A] [TypeRep B] (h : TypeRep.rep A = TypeRep.rep B) (x : A) : B :=
  ULift.down (cast (uniqueTypeRep A B h) (ULift.up x))

/-- Try casting based on equality of type representations. -/
def tryCast {A : Type u} {B : Type w} [repA : TypeRep A] [repB : TypeRep B] (x : A) : Option B :=
  if h : TypeRep.rep A = TypeRep.rep B then
    some (rcast h x)
  else
    none

/-- Boolean equality between elements in different types. -/
def beq_generic {A : Type u} {B : Type w} [repA : TypeRep A] [repB : TypeRep B] [beqB : BEq B] (x : A) (y : B) : Bool :=
  match tryCast x with
  | some y' => y' == y
  | none => false

/-- Boolean equality between elements in different types. -/
infix:50 " === " => beq_generic

instance : TypeRep Unit where
  rep := Rep.atomic "Unit"

instance : TypeRep Bool where
  rep := Rep.atomic "Bool"

instance : TypeRep Nat where
  rep := Rep.atomic "Nat"

instance : TypeRep String where
  rep := Rep.atomic "String"

instance {α} [TypeRep α]: TypeRep (List α) where
  rep := Rep.composite "List" [TypeRep.rep α]

instance {α} [TypeRep α]: TypeRep (Array α) where
  rep := Rep.composite "Array" [TypeRep.rep α]

instance {α} [TypeRep α]: TypeRep (Option α) where
  rep := Rep.composite "Option" [TypeRep.rep α]

instance {α β} [TypeRep α] [TypeRep β]: TypeRep (Prod α β) where
  rep := Rep.composite "Prod" [TypeRep.rep α, TypeRep.rep β]

instance {α β} [TypeRep α] [TypeRep β]: TypeRep (Sum α β) where
  rep := Rep.composite "Sum" [TypeRep.rep α, TypeRep.rep β]

instance {α β} [TypeRep α] [TypeRep β] : TypeRep (Except α β) where
  rep := Rep.composite "Except" [TypeRep.rep α, TypeRep.rep β]

instance {α} [TypeRep α] : TypeRep (ULift α) where
  rep := Rep.composite "ULift" [TypeRep.rep α]
