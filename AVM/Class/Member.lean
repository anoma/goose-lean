import Prelude
import AVM.Object
import AVM.Class.Label

namespace AVM.Class

structure Constructor {lab : Class.Label} (constrId : lab.ConstructorId) where
  /-- Object created in the constructor call. -/
  created : constrId.Args.type → ObjectData lab
  /-- Extra constructor logic. The constructor invariant is combined with
      auto-generated constructor body constraints to create the constructor logic. -/
  invariant : constrId.Args.type → Bool

structure Destructor {lab : Class.Label} (destructorId : lab.DestructorId) where
  /-- Extra destructor logic. -/
  invariant : (self : Object lab) → destructorId.Args.type → Bool

structure Method {lab : Class.Label.{u}} (methodId : lab.MethodId) : Type (u + 1) where
  /-- Objects created in the method call (the new self/selves). -/
  created : (self : Object lab) → methodId.Args.type → List SomeObject
  /-- Extra method logic. The method invariant is combined with auto-generated
      method body constraints to create the method logic. -/
  invariant : (self : Object lab) → methodId.Args.type → Bool

/-- A class member is a constructor, a destructor or a method. -/
inductive Member (lab : Class.Label) where
  | constructor (constrId : lab.ConstructorId) (constr : Constructor constrId) : Member lab
  | destructor (destrId : lab.DestructorId) (destr : Destructor destrId) : Member lab
  | method (methodId : lab.MethodId) (method : Method methodId) : Member lab
