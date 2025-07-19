import AVM.Intent
import AVM.Class.Label
import Prelude

namespace AVM.Class

structure Constructor {lab : Label} (constrId : lab.ConstructorId) where
  /-- Extra constructor logic. The constructor invariant is combined with
      auto-generated constructor body constraints to create the constructor logic. -/
  invariant : constrId.Args.type → Bool
  /-- Objects created in the constructor call. -/
  created : constrId.Args.type → Object lab

structure Method {lab : Label.{u}} (methodId : lab.MethodId) : Type (u + 1) where
  /-- Extra method logic. The method invariant is combined with auto-generated
      method body constraints to create the method logic. -/
  invariant : (self : Object lab) → methodId.Args.type → Bool
  /-- Objects created in the method call. -/
  created : (self : Object lab) → methodId.Args.type → List SomeObject

structure Destructor {lab : Label} (destructorId : lab.DestructorId) where
  /-- Extra destructor logic. -/
  invariant : (self : Object lab) → destructorId.Args.type → Bool
