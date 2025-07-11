import AVM.Object
import AVM.Intent
import AVM.Class.Label

namespace AVM.Class

structure Constructor {lab : Label} (constrId : lab.ConstructorId) where
  /-- Extra constructor logic. The constructor invariant is combined with
      auto-generated constructor body constraints to create the constructor logic. -/
  invariant : constrId.Args.type → Bool
  /-- Objects created in the constructor call. -/
  created : constrId.Args.type → Object lab

structure Method {lab : Label} (methodId : lab.MethodId) where
  /-- Extra method logic. The method invariant is combined with auto-generated
      method body constraints to create the method logic. -/
  invariant : (self : Object lab) → methodId.Args.type → Bool
  /-- Objects created in the method call. -/
  created : (self : Object lab) → methodId.Args.type → List SomeObject

structure Destructor {lab : Label} (destructorId : lab.DestructorId) where
  /-- Extra destructor logic. -/
  invariant : (self : Object lab) → destructorId.Args.type → Bool

/-- A class member is a method, a constructor or an intent. A single intent can
  be a member in multiple classes, but each constructor and method is a member
  of a unique class. -/
inductive Member (lab : Label) where
  | constructor (constrId : lab.ConstructorId) (constr : Constructor constrId) : Member lab
  | method (methodId : lab.MethodId) (method : Method methodId) : Member lab
  | intent (intent : Intent) : Member lab
