
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

private def getUniverseLevel (ty : Expr) : Option Level :=
  match ty with
  | .sort l =>
      match l.toNat with
      | some n => some <| Level.ofNat n.pred
      | none => none
  | _ => none

private def dropParams (n : Nat) (ty : Expr) : List Expr × Expr :=
  if n > 0 then
    match ty with
    | .forallE _name ty' body _bi =>
        let (env, body') := dropParams (n - 1) body
        (ty' :: env, body')
    | _ => ([], ty)
  else
    ([], ty)

-- NOTE: this is not fully correct (need to handle instance argument to TypeRep.rep)
private def mkConstrRepArgs (shift : Nat) (acc : List Expr) (ty : Expr) : MetaM (List Expr) :=
  match ty with
  | .forallE _name ty' body _bi => do
    let kind ← match ty' with
      | .bvar n => pure acc[n]!
      | _ => Meta.inferType ty'
    let ty'' := ty'.lowerLooseBVars shift shift
    let lvl : Level := getUniverseLevel kind |>.getD Level.zero
    let inst ← match ty' with
      | .bvar n => pure <| mkBVar n
      | _ => pure ty'' -- Meta.synthInstance (← mkAppM ``TypeRep #[ty'])
    let arg := mkApp2 (mkConst ``TypeRep.rep [lvl]) ty'' inst
    mkConstrRepArgs (shift + 1) (arg :: acc) body
  | _ =>
    pure <| acc.reverse

private def mkConstrRep (ctor : Name) (ctorType : Expr) (paramsNum : Nat) : MetaM Expr := do
  let nameLit : Expr := Expr.lit (Literal.strVal ctor.toString)
  let (tys, ty) := dropParams paramsNum ctorType
  let repArgs ← mkConstrRepArgs 0 tys.reverse ty
  let argsList : Expr ← liftMetaM $ Meta.mkListLit (mkConst ``Rep) (repArgs.drop paramsNum)
  pure <| mkApp2 (mkConst ``Constr.Rep.mk) nameLit argsList

private def mkInstanceHelper
  (mkBinder : Name → BinderInfo → Expr → Expr → Expr)
  (mkCore : (paramShift : Nat) → Level → (indTy : Expr) → (indApp : Expr) → Expr)
  (iv : InductiveVal)
  : MetaM Expr := do
  -- Turn `∀ (α₁ : u₁) … (αₙ : uₙ), T α₁ … αₙ` into an Array of binders + the body.
  let bs ← forallTelescopeReducing iv.type fun fvars _body =>
    fvars.mapM (fun fvar => do
      let type ← Meta.inferType fvar
      pure (← mkFreshUserName `α, BinderInfo.implicit, type))
  let params := bs.toList.take iv.numParams
  -- Each `bs[i] : (nm : Name, bi : BinderInfo, ty : Expr)`

  unless iv.numIndices == 0 do
    throwError "Indexed types not supported."
  let vars : List Name := params.map (fun (nm, _, _) => nm)
  let vars' : List Name ← params.mapM (fun _ => mkFreshUserName `i)
  let types : List Expr := params.map (fun (_, _, ty) => ty)

  -- Build `T α₁ … αₙ`
  let levels := iv.levelParams.map Level.param
  let level := match levels with
    | [u] => u
    | u :: levels' => levels'.foldr Level.max u
    | [] => getUniverseLevel iv.type |>.getD Level.zero
  let indTy : Expr := mkConst iv.name levels
  let indApp : Expr := mkAppN indTy ((Array.range' vars'.length vars.length).reverse.map mkBVar)

  let core := mkCore vars'.length level indTy indApp

  -- Wrap each `[TypeRep αᵢ]` using `BinderInfo.instImplicit`
  let withInst : Expr := (vars'.zip (List.range vars.length)).foldr
    (fun (var, idx) acc =>
      mkBinder var BinderInfo.instImplicit
        (mkApp (mkConst ``TypeRep [level]) (mkBVar idx))
        acc)
    core

  -- Wrap the `{α₁ … αₙ}` implicit parameters
  let fullValue : Expr := (vars.zip types).foldr
    (fun (var, ty) acc =>
      mkBinder var BinderInfo.implicit ty acc)
    withInst

  return fullValue

private def mkInstanceType (iv : InductiveVal) : MetaM Expr := do
  let mkCore _ (level : Level) _ (indApp : Expr) := mkApp (mkConst ``TypeRep [level]) indApp
  mkInstanceHelper (mkBinder := mkForall) mkCore iv

private def mkInstanceBody (iv : InductiveVal) (_e : Expr) : MetaM Expr := do
  let mkCore _paramShift level _ indApp :=
    --let indApp' := indApp.liftLooseBVars 0 1
    --let indApp'' := indApp.liftLooseBVars 0 2
    -- let e' := e.liftLooseBVars 0 (paramShift + 2)
    let e' := mkApp (mkConst ``Rep.atomic) (mkStrLit iv.name.toString)
    --mkLambda `A BinderInfo.default (Expr.sort level.succ)
      -- (mkLambda `self BinderInfo.instImplicit (mkApp (mkConst ``TypeRep [level]) indApp')
    (mkApp2 (mkConst ``TypeRep.mk [level]) indApp e')
  mkInstanceHelper (mkBinder := mkLambda) mkCore iv

/-- Derives a TypeRep instance for a given type. -/
syntax (name := deriveTypeRepCmd) "derive_type_rep " ident : command

@[command_elab deriveTypeRepCmd]
def elabDeriveTypeRep : CommandElab := fun stx => withFreshMacroScope do
  match stx with
  | `(derive_type_rep $name:ident) =>
    let tName := stx[1].getId
    let declName ← liftCoreM <| mkFreshUserName `inst

    -- lookup the inductive
    let env ← getEnv
    let some cinfo := env.find? tName
      | throwError "derive_type_rep: `{tName}` not found"
    let info ← match cinfo with
      | .inductInfo info => pure info
      | _ => throwError "derive_type_rep: `{tName}` is not an inductive type"

    let type ← liftTermElabM <| mkInstanceType info

    -- build Constr.Rep for each constructor
    let ctorReps ← info.ctors.mapM fun ctorName => do
      let some ctorCinfo := env.find? ctorName
        | throwError "derive_type_rep: constructor `{ctorName}` not found"
      let ctorInfo ← match ctorCinfo with
        | .ctorInfo info => pure info
        | _ => throwError "derive_type_rep: `{ctorName}` is not a constructor"
      liftTermElabM <| mkConstrRep ctorName ctorInfo.type info.numParams

    -- assemble `Rep.composite "T" [ … ]`
    let nameLit : Expr := Expr.lit (Literal.strVal tName.toString)
    let ctorList : Expr ← liftTermElabM <| mkListLit (mkConst ``Constr.Rep) ctorReps
    let repConstr : Expr := Expr.app (Expr.app (mkConst ``Rep.composite) nameLit) ctorList

    let repBody : Expr ← liftTermElabM <| mkInstanceBody info repConstr

    let decl :=
      Declaration.defnDecl {
        name        := declName
        levelParams := info.levelParams
        type        := type
        value       := repBody
        hints       := ReducibilityHints.abbrev
        safety      := DefinitionSafety.safe
      }

    -- Add the declaration to the environment
    liftTermElabM <| addAndCompile decl

    -- Register it as an instance
    liftTermElabM <| addInstance declName (attrKind := AttributeKind.global) (prio := 10)
  | _ =>
      throwError "Invalid syntax for `derive_type_rep`. Expected `derive_type_rep <TypeName>`."

private axiom uniqueTypeRep (A B : Type u) [TypeRep A] [TypeRep B] : TypeRep.rep A = TypeRep.rep B → A = B

/-- Casting based on equality of type representations. -/
def rcast {A B : Type u} [TypeRep A] [TypeRep B] (h : TypeRep.rep A = TypeRep.rep B) (x : A) : B :=
  cast (uniqueTypeRep A B h) x

def tryCast {A B : Type u} [TypeRep A] [TypeRep B] (x : A) : Option B :=
  if h : TypeRep.rep A = TypeRep.rep B then
    some (rcast h x)
  else
    none

instance : TypeRep Unit where
  rep := Rep.atomic "Unit"

derive_type_rep Nat
derive_type_rep String
derive_type_rep List
derive_type_rep Option

-- Examples:
-- #eval (inferInstance : TypeRep Nat).rep
-- #eval (inferInstance : TypeRep String).rep
-- #eval (inferInstance : TypeRep (List Nat)).rep

def beqCast {A B : Type u} [TypeRep A] [TypeRep B] [BEq B] (x : A) (y : B) : Bool :=
  match tryCast x with
  | some y' => y' == y
  | none => false
