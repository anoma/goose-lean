import Anoma.Resource
import AVM.Class.Label
import Init.Data.Fin.Lemmas
import AVM.Object
import AVM.Class

namespace AVM

open Class

inductive Program.Return where
  | Object
  | Unit

inductive Value : Type (u + 1) where
  | Object : {clab : Class.Label} → Object clab → Value

def LocalVars (n : Nat) : Type (u + 1) := Vector Value n

namespace LocalVars

def extend (v : Value) (l : LocalVars n) : LocalVars (n + 1) :=
    l.push v

infixr:67 " :: " => extend

end LocalVars

inductive Program : {n : Nat} → LocalVars n → Type (u + 1) where
  | constructorCall
      {Γ : LocalVars n}
      {clab : Class.Label.{u}}
      {constructorId : clab.ConstructorId}
      (constr : Constructor constructorId)
      (args : constructorId.Args.type)
      (prog : Program (.Object (constr.created args) :: Γ))
      : Program Γ
  | destructorCall
      {Γ : LocalVars n}
      {clab : Class.Label.{u}}
      {destructorId : clab.DestructorId}
      (destr : Destructor destructorId)
      (args : destructorId.Args.type)
      (prog : Program Γ)
      : Program Γ
  | methodCall
     {Γ : LocalVars n}
     {clab : Class.Label.{u}}
     {methodId : clab.MethodId}
     (method : Method methodId)
     (args : methodId.Args.type)
     (self : Object clab)
     (prog : Program Γ)
     : Program Γ

def TopProgram : Type (u + 1) := Program (Vector.emptyWithCapacity 0)
