import AVM.Program

namespace AVM.Class

structure Constructor {lab : Ecosystem.Label} (cid : lab.ClassId) (constrId : cid.label.ConstructorId) : Type 1 where
  /-- Constructor call body. -/
  body : constrId.Args.type → Program.{0} lab (ObjectData cid)
  /-- Extra constructor logic. The constructor invariant is combined with
      auto-generated constructor body constraints to create the constructor logic. -/
  invariant : constrId.Args.type → Bool

structure Destructor {lab : Ecosystem.Label} (cid : lab.ClassId) (destructorId : cid.label.DestructorId) : Type 1 where
  /-- Destructor call body. -/
  body : (self : Object cid) → destructorId.Args.type → Program.{0} lab PUnit
  /-- Extra destructor logic. -/
  invariant : (self : Object cid) → destructorId.Args.type → Bool

structure Method {lab : Ecosystem.Label} (cid : lab.ClassId) (methodId : cid.label.MethodId) : Type 1 where
  /-- Method call body. -/
  body : (self : Object cid) → methodId.Args.type → Program lab (Object cid)
  /-- Extra method logic. The method invariant is combined with auto-generated
      method body constraints to create the method logic. -/
  invariant : (self : Object cid) → methodId.Args.type → Bool

/-- A class member is a constructor, a destructor or a method. -/
inductive Member {lab : Ecosystem.Label} (cid : lab.ClassId) where
  | constructor (constrId : cid.label.ConstructorId) (constr : Constructor cid constrId)
  | destructor (destrId : cid.label.DestructorId) (destr : Destructor cid destrId)
  | method (methodId : cid.label.MethodId) (method : Method cid methodId)
