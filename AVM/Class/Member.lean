import AVM.Object
import AVM.Class.Label

namespace AVM.Class

def Constructor.Args {lab : Label} (constrId : lab.ConstructorId) : Type :=
  lab.ConstructorArgs constrId

structure Constructor {lab : Label} (constrId : lab.ConstructorId) where
  /-- Extra constructor logic. It is combined with auto-generated constructor
      logic to create the complete constructor logic. -/
  extraLogic : constrId.Args → Bool
  /-- Objects created in the constructor call. -/
  created : constrId.Args → Object lab

structure Method {lab : Label} (methodId : lab.MethodId) where
  /-- Extra method logic. It is combined with auto-generated method logic to
      create the complete method logic. -/
  extraLogic : (self : Object lab) → methodId.Args → Bool
  /-- Objects created in the method call. -/
  created : (self : Object lab) → methodId.Args → List SomeObject

/-- A class member is a method or a constructor. -/
inductive Member (lab : Label) : Type 1 where
  | constructor (constrId : lab.ConstructorId) (constr : Constructor constrId) : Member lab
  | method (methodId : lab.MethodId) (method : Method methodId) : Member lab
