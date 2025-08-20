import Mathlib.Control.Random
import Prelude
import AVM.Object
import AVM.Class.Label
import AVM.Ecosystem.Label

namespace AVM.Class

inductive Member.Call (lab : Ecosystem.Label) where
  | constructor (cid : lab.ClassId) (constrId : cid.label.ConstructorId) (newId : ObjectId)
  | destructor (cid : lab.ClassId) (destrId : cid.label.DestructorId) (selfId : ObjectId)
  | method (cid : lab.ClassId) (methodId : cid.label.MethodId) (selfId : ObjectId)

structure Result.{u} (lab : Ecosystem.Label) (ReturnType : Type u) where
  calls : List (Member.Call lab)
  returnValue : ReturnType

structure Constructor {lab : Ecosystem.Label} (cid : lab.ClassId) (constrId : cid.label.ConstructorId) where
  /-- Constructor call body. -/
  body : constrId.Args.type → Result lab (ObjectData cid.label)
  /-- Extra constructor logic. The constructor invariant is combined with
      auto-generated constructor body constraints to create the constructor logic. -/
  invariant : constrId.Args.type → Bool

structure Destructor.{u} {lab : Ecosystem.Label} (cid : lab.ClassId) (destructorId : cid.label.DestructorId) : Type (u + 1) where
  /-- Destructor call body. -/
  body : (self : Object cid.label) → destructorId.Args.type → Result.{u} lab PUnit
  /-- Extra destructor logic. -/
  invariant : (self : Object cid.label) → destructorId.Args.type → Bool

structure Method {lab : Ecosystem.Label} (cid : lab.ClassId) (methodId : cid.label.MethodId) : Type (u + 1) where
  /-- Method call body. -/
  body : (self : Object cid.label) → methodId.Args.type → Result lab (Object cid.label)
  /-- Extra method logic. The method invariant is combined with auto-generated
      method body constraints to create the method logic. -/
  invariant : (self : Object cid.label) → methodId.Args.type → Bool

/-- A class member is a constructor, a destructor or a method. -/
inductive Member {lab : Ecosystem.Label} (cid : lab.ClassId) where
  | constructor (constrId : cid.label.ConstructorId) (constr : Constructor cid constrId)
  | destructor (destrId : cid.label.DestructorId) (destr : Destructor cid destrId)
  | method (methodId : cid.label.MethodId) (method : Method cid methodId)
