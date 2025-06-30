
import Lean
import Prelude.List

open Lean Elab Command Meta

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

class TypeRep (A : Type u) where
  /-- A unique representation of the type. -/
  rep : Rep

/-- Build a `Constr.Rep` term for constructor `ctor` whose argument types are `argTs`. -/
private def mkConstrRep {m} [MonadLiftT MetaM m] [Monad m] (ctor : Name) (argTs : Array Expr) : m Expr := do
  let nameLit : Expr := Expr.lit (Literal.strVal ctor.toString)
  let argsList : Expr ← liftMetaM $ Meta.mkListLit (mkConst ``Rep) (argTs.toList.map (·.app (mkConst ``TypeRep.rep)))
  pure <| mkApp2 (mkConst ``Constr.Rep.mk) nameLit argsList

private def mkInstanceTypeWithConstraints (iv : InductiveVal) : MetaM Expr := do
  -- 1) Turn `∀ (α₁ : u₁) … (αₙ : uₙ), T α₁ … αₙ` into an Array of binders + the body.
  let bs ← forallTelescopeReducing iv.type fun fvars body =>
    fvars.mapM (fun fvar => do
      let type ← Meta.inferType fvar
      pure (← mkFreshUserName `α, BinderInfo.implicit, type))
  let paramBs := bs.toList.take iv.numParams
    -- Each `bs[i] : (nm : Name, bi : BinderInfo, ty : Expr)`

  -- 2) Introduce a fresh local for each αᵢ
  let fvars ← paramBs.mapM fun (nm, bi, ty) =>
    withLocalDecl nm bi ty fun x => pure sorry

  -- 3) Build `T α₁ … αₙ`
  let indApp : Expr := mkAppN (mkConst iv.name) (fvars.toArray.map mkFVar)

  -- 4) Build `TypeRep (T α₁ … αₙ)`
  let core : Expr := mkApp (mkConst ``TypeRep) indApp

  -- 5) Wrap each `[TypeRep αᵢ]` using `BinderInfo.instImplicit`
  --    We zip binders with their fvars so we know which FVar to refer to.
  let withInst : Expr := (paramBs.zip fvars).foldr
    (fun ((nm, _, _), fvar) acc =>
      -- ∀ [TypeRep αᵢ], acc
      mkForall nm BinderInfo.instImplicit
        (mkApp (mkConst ``TypeRep) (mkFVar fvar))
        acc)
    core

  -- 6) Finally wrap the `{α₁ … αₙ}` implicit parameters
  let fullType : Expr := paramBs.foldr
    (fun (nm, _, ty) acc =>
      -- ∀ {nm : ty}, acc
      mkForall nm BinderInfo.implicit ty acc)
    withInst

  return fullType

/-- Derives a TypeRep instance for a given type. -/
-- TODO: this should derive a generic instance for parameterised types (e.g.
-- TypeRep A => TypeRep (List A)), currently just uses unique type name (e.g.
-- List).
syntax (name := deriveTypeRepCmd) "derive_type_rep " ident : command

@[command_elab deriveTypeRepCmd]
def elabDeriveTypeRep : CommandElab := fun stx => withFreshMacroScope do
  match stx with
  | `(derive_type_rep $name:ident) =>
    let tName := stx[1].getId
    let env ← getEnv
    -- lookup the inductive
    let some cinfo := env.find? tName
      | throwError "derive_type_rep: `{tName}` not found"
    let info ← match cinfo with
      | .inductInfo info => pure info
      | _ => throwError "derive_type_rep: `{tName}` is not an inductive type"

    let type ← liftTermElabM <| mkInstanceTypeWithConstraints info

    -- build Constr.Rep for each constructor
    let ctorReps ← info.ctors.mapM fun ctorName => do
      let some ctorCinfo := env.find? ctorName
        | throwError "derive_type_rep: constructor `{ctorName}` not found"
      let ctorInfo ← match ctorCinfo with
        | .ctorInfo info => pure info
        | _ => throwError "derive_type_rep: `{ctorName}` is not a constructor"
      let argTys ← liftTermElabM <| forallTelescopeReducing ctorInfo.type fun fvars body => do
        -- fvars : Array Expr  -- fresh local constants for each binder
        -- body  : Expr       -- the result type with those fvars
        fvars.mapM (fun fvar => Meta.inferType fvar)
      liftTermElabM <| mkConstrRep ctorName argTys

    -- assemble `Rep.composite "T" [ … ]`
    let nameLit : Expr := Expr.lit (Literal.strVal tName.toString)
    let ctorList : Expr ← liftTermElabM <| mkListLit (mkConst ``Constr.Rep) ctorReps
    let repBody : Expr := Expr.app (mkConst ``Rep.composite) (Expr.app nameLit ctorList)

    let decl :=
      Declaration.defnDecl {
        name        := tName
        levelParams := []
        type        := type
        value       := valExpr
        hints       := ReducibilityHints.abbrev
        safety      := DefinitionSafety.safe
      }

    -- 6. Add the declaration to the environment
    liftTermElabM <| addAndCompile decl

    -- 7. Register it as an instance
    addInstance name

    let ctxStx : Syntax :=
      mkNode `Lean.Parser.Term.instBinder
        classConstraints

    elabCommand <|
      ← `(instance { $(paramIdents)* } $ctxStx  : TypeRep $name $paramIdents:ident* := ⟨ $(Quote.quote repBody):term ⟩)
  | _ =>
      throwError "Invalid syntax for `derive_type_rep`. Expected `derive_type_rep <TypeName>`."

private axiom uniqueTypeRep (A B : Type) [TypeRep A] [TypeRep B] : TypeRep.rep A = TypeRep.rep B → A = B

/-- Casting based on equality of type representations. -/
def rcast {A B : Type} [TypeRep A] [TypeRep B] (h : TypeRep.rep A = TypeRep.rep B) (x : A) : B :=
  cast (uniqueTypeRep A B h) x

def tryCast {A B : Type} [TypeRep A] [TypeRep B] (x : A) : Option B :=
  if h : TypeRep.rep A = TypeRep.rep B then
    some (rcast h x)
  else
    none

derive_type_rep Nat
derive_type_rep String
-- derive_type_rep List

-- Examples:
-- #eval (inferInstance : TypeRep Nat).rep
-- #eval (inferInstance : TypeRep String).rep
-- #eval (inferInstance : TypeRep (List Nat)).rep
