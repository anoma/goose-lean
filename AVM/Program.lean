import Anoma.Resource
import AVM.Class.Label
import Init.Data.Fin.Lemmas
import AVM.Object
import AVM.Class
import AVM.Ecosystem

namespace AVM

open Class

inductive PType : Type (u + 1) where
  | Object : Class.Label → PType
  | Reference : Class.Label → PType
  | SomeType : SomeType → PType
  | Program : (args : List PType) → (ret : PType) →  PType

def LocalVars (n : Nat) : Type (u + 1) := Vector PType n

namespace LocalVars

def extend (v : PType) (l : LocalVars n) : LocalVars (n + 1) :=
    l.push v

infixr:67 " ▹ " => extend

end LocalVars

structure LocalVar {n : Nat} (Γ : LocalVars n) (ty : PType) : Type where
  ix : Fin n
  typed : Γ.get ix = ty := by rfl

inductive Expr (Γ : LocalVars n) : PType → Type (u + 1) where
  | constRef {lab : Class.Label} (ref : Reference lab) : Expr Γ (.Reference lab)
  | var {ty : PType} (v : LocalVar Γ ty) : Expr Γ ty
  | const {t : SomeType} : t.type → Expr Γ (.SomeType t)

inductive Exprs (Γ : LocalVars n) : (len : Nat) → Type (u + 1) where
  | nil : Exprs Γ 0
  | cons (ty : PType) {len : Nat} (e : Expr Γ ty) (es : Exprs Γ len) : Exprs Γ (len + 1)

def Exprs.typeList {Γ : LocalVars n} (es : Exprs Γ l) : List PType := match es with
  | .nil => []
  | .cons ty _e es => ty :: es.typeList

def typeOfExt : PType.{u} → Type u := fun
  | .Object l => Object l
  | .Program args ret => args.map typeOfExt |>.Product → typeOfExt ret
  | .Reference l => ULift (Reference l)
  | .SomeType l => l.type

def typesOf {Γ : LocalVars n} : Exprs Γ l → LocalVars l := fun
  | .nil => Vector.ofFn fun x => nomatch x
  | .cons ty _e es => typesOf es |>.push ty

def typesOfExt.{u} (tys : List PType) : Type u := tys.map typeOfExt |>.Product

infixr:67 " ::: " => Exprs.cons

instance LocalVars.instMembership {n : Nat} : Membership PType (LocalVars n) := Vector.instMembership

inductive Program.{u} : {n : Nat} → LocalVars.{u} n → (ret : PType) → Type (u + 1) where
  -- FIXME I haven't still figured out a way to formalize constructor calls.
  -- The sort reification that I've done here should be replaced.
  -- But then, how does one specify the object that's built in a constructor?
  -- It's tempting to use Lean4 records, but then how do we pass arguments that are created during program execution?
  -- I think the solution is to add Object expressions to Expr. But this seems complicated
  -- There is probably a better way
  | callConstructor
     {Γ : LocalVars.{u} n}
     {ret : PType}
     {clab : Class.Label}
     {nargs : Nat}
     (args : Exprs Γ nargs)
     (fn : typesOfExt args.typeList → Object clab)
     (prog : Program (.Reference clab ▹ Γ) ret)
     : Program Γ ret
  | let
     {Γ : LocalVars n}
     {ret : PType}
     {exprTy : PType}
     (expr : Expr Γ exprTy)
     (prog : Program (exprTy ▹ Γ) ret)
     : Program Γ ret
  | call
     {Γ : LocalVars n}
     {ret : PType}
     {ret' : PType}
     {nargs : Nat}
     (args : Exprs Γ nargs)
     (fn : Expr Γ (.Program (typesOf args).toList ret'))
     (prog : Program (ret' ▹ Γ) ret)
     : Program Γ ret
  | pure
     {Γ : LocalVars n}
     {ret : PType}
     (e : Expr Γ ret)
     : Program Γ ret
  | store
     {Γ : LocalVars n}
     {ret : PType}
     {clab : Class.Label.{u}}
     (ref : Expr Γ (.Reference clab))
     (obj : Object clab)
     (prog : Program Γ ret)
     : Program Γ ret
  | allocate
     {Γ : LocalVars n}
     {ret : PType}
     (clab : Class.Label.{u})
     (prog : Program (.Reference clab ▹ Γ) ret)
     : Program Γ ret
  | deref
     {Γ : LocalVars n}
     {ret : PType}
     {clab : Class.Label.{u}}
     (ref : Reference clab)
     (prog : Program (.Object clab ▹ Γ) ret)
     : Program Γ ret

def TopProgram (ret : PType) : Type (u + 1) :=
    Program (Vector.emptyWithCapacity 0) ret

def Program.noop {Γ : LocalVars n} : Program Γ (.SomeType ⟨Unit⟩) :=
  Program.pure (.const .unit)
