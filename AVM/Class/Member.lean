import Mathlib.Control.Random
import Prelude
import AVM.Object
import AVM.Class.Label
import AVM.Ecosystem.Label
import AVM.Task.Parameters

namespace AVM.Class

inductive Member.Body.{u} (lab : Ecosystem.Label) (ReturnType : Type u) : Task.Parameters.{u} → Type (u + 1) where
  | constructor {params : Task.Parameters} (cid : lab.ClassId) (constrId : cid.label.ConstructorId) (args : params.Product → constrId.Args.type) (next : Member.Body lab ReturnType params.snocGenId) : Member.Body lab ReturnType params
  | destructor {params : Task.Parameters} (cid : lab.ClassId) (destrId : cid.label.DestructorId) (selfId : params.Product → ObjectId) (args : params.Product → destrId.Args.type) (next : Member.Body lab ReturnType params) : Member.Body lab ReturnType params
  | method {params : Task.Parameters} (cid : lab.ClassId) (methodId : cid.label.MethodId) (selfId : params.Product → ObjectId) (args : params.Product → methodId.Args.type) (next : Member.Body lab ReturnType params) : Member.Body lab ReturnType params
  | fetch {params : Task.Parameters} (objId : params.Product → TypedObjectId) (next : Member.Body lab ReturnType (params.snocFetch objId)) : Member.Body lab ReturnType params
  | return {params : Task.Parameters} (val : params.Product → ReturnType) : Member.Body lab ReturnType params

structure Constructor {lab : Ecosystem.Label} (cid : lab.ClassId) (constrId : cid.label.ConstructorId) where
  /-- Constructor call body. -/
  body : constrId.Args.type → Member.Body lab (ObjectData cid.label) .empty
  /-- Extra constructor logic. The constructor invariant is combined with
      auto-generated constructor body constraints to create the constructor logic. -/
  invariant : constrId.Args.type → Bool

structure Destructor.{u} {lab : Ecosystem.Label} (cid : lab.ClassId) (destructorId : cid.label.DestructorId) : Type (u + 1) where
  /-- Destructor call body. -/
  body : (self : Object cid.label) → destructorId.Args.type → Member.Body lab PUnit .empty
  /-- Extra destructor logic. -/
  invariant : (self : Object cid.label) → destructorId.Args.type → Bool

structure Method {lab : Ecosystem.Label} (cid : lab.ClassId) (methodId : cid.label.MethodId) : Type (u + 1) where
  /-- Method call body. -/
  body : (self : Object cid.label) → methodId.Args.type → Member.Body lab (Object cid.label) .empty
  /-- Extra method logic. The method invariant is combined with auto-generated
      method body constraints to create the method logic. -/
  invariant : (self : Object cid.label) → methodId.Args.type → Bool

/-- A class member is a constructor, a destructor or a method. -/
inductive Member {lab : Ecosystem.Label} (cid : lab.ClassId) where
  | constructor (constrId : cid.label.ConstructorId) (constr : Constructor cid constrId)
  | destructor (destrId : cid.label.DestructorId) (destr : Destructor cid destrId)
  | method (methodId : cid.label.MethodId) (method : Method cid methodId)
