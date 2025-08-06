import Anoma.Resource
import AVM.Class.Label
import Init.Data.Fin.Lemmas
import AVM.Object
import AVM.Class

namespace AVM

open Class

inductive PType : Type (u + 1) where
  | Object : Class.Label → PType
  | Reference : Class.Label → PType

def LocalVars (n : Nat) : Type (u + 1) := Vector PType n

namespace LocalVars

def extend (v : PType) (l : LocalVars n) : LocalVars (n + 1) :=
    l.push v

infixr:67 " :: " => extend

end LocalVars

structure LocalVar {n : Nat} (Γ : LocalVars n) (ty : PType) : Type where
  ix : Fin n
  typed : Γ.get ix = ty

inductive Expr {n : Nat} (Γ : LocalVars n) : PType → Type (u + 1) where
  | constRef {lab : Class.Label} (ref : Reference lab) : Expr Γ (.Reference lab)
  | var {ty : PType} (v : LocalVar Γ ty) : Expr Γ ty

inductive Program : {n : Nat} → LocalVars n → Type (u + 1) where
  | constructorCall
      {Γ : LocalVars n}
      {clab : Class.Label.{u}}
      {constructorId : clab.ConstructorId}
      (constr : Constructor constructorId)
      (args : constructorId.Args.type)
      (prog : Program (.Reference clab :: Γ))
      : Program Γ
  | destructorCall
      {Γ : LocalVars n}
      {clab : Class.Label.{u}}
      {destructorId : clab.DestructorId}
      (destr : Destructor destructorId)
      (args : destructorId.Args.type)
      (self : Expr Γ (.Reference clab))
      (prog : Program Γ)
      : Program Γ
  | methodCall
     {Γ : LocalVars n}
     {clab : Class.Label.{u}}
     {methodId : clab.MethodId}
     (method : Method methodId)
     (args : methodId.Args.type)
     (self : Expr Γ (.Reference clab))
     (prog : Program Γ)
     : Program Γ
  | deref
     {Γ : LocalVars n}
     {clab : Class.Label.{u}}
     (ref : Reference clab)
     (prog : Program (.Object clab :: Γ))
     : Program Γ

def TopProgram : Type (u + 1) :=
    Program (Vector.emptyWithCapacity 0)
