import AVM.Intent
import AVM.Class.Label
import Prelude

namespace AVM.Class

structure Constructor {lab : Class.Label} (constrId : lab.ConstructorId) where
  /-- Extra constructor logic. The constructor invariant is combined with
      auto-generated constructor body constraints to create the constructor logic. -/
  invariant : constrId.Args.type → Bool
  /-- Object created in the constructor call. -/
  created : constrId.Args.type → Object lab

structure Destructor {lab : Class.Label} (destructorId : lab.DestructorId) where
  /-- Extra destructor logic. -/
  invariant : (self : Object lab) → destructorId.Args.type → Bool

structure Method {lab : Class.Label.{u}} (methodId : lab.MethodId) : Type (u + 1) where
  /-- Extra method logic. The method invariant is combined with auto-generated
      method body constraints to create the method logic. -/
  invariant : (self : Object lab) → methodId.Args.type → Bool
  /-- Objects created in the method call. -/
  created : (self : Object lab) → methodId.Args.type → List SomeObject

/-- A class member is a constructor, a destructor, a method or an intent. A
  single intent can be a member in multiple classes, but each constructor,
  destructor and method is a member of a unique class. -/
inductive Member (lab : Class.Label) where
  | constructor (constrId : lab.ConstructorId) (constr : Constructor constrId) : Member lab
  | destructor (destrId : lab.DestructorId) (destr : Destructor destrId) : Member lab
  | method (methodId : lab.MethodId) (method : Method methodId) : Member lab
  | intent (ilab : Intent.Label) (_ : ilab ∈ lab.intentLabels) (intent : Intent ilab) : Member lab
