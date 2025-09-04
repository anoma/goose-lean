import AVM
import Applib.Surface.Object
import Applib.Surface.Reference

namespace Applib

open AVM

inductive Program (lab : Ecosystem.Label) (ReturnType : Type) where
  | create
      (C : Type)
      (cid : lab.ClassId)
      (constrId : cid.label.ConstructorId)
      (args : constrId.Args.type)
      (next : ObjectId → Program lab ReturnType)
      : Program lab ReturnType
  | destroy
      (cid : lab.ClassId)
      (destrId : cid.label.DestructorId)
      (selfId : ObjectId)
      (args : destrId.Args.type)
      (next : Program lab ReturnType)
      : Program lab ReturnType
  | call
      (cid : lab.ClassId)
      (methodId : cid.label.MethodId)
      (selfId : ObjectId)
      (args : methodId.Args.type)
      (next : Program lab ReturnType)
      : Program lab ReturnType
  | fetch
      (C : Type)
      [i : IsObject C]
      (objId : ObjectId)
      (next : C → Program lab ReturnType)
      : Program lab ReturnType
  | return
      (val : ReturnType)
      : Program lab ReturnType

def Program.toAVM {lab ReturnType} (prog : Program lab ReturnType) : AVM.Program lab ReturnType :=
  match prog with
  | .create _ cid constrId args next =>
    .constructor cid constrId args (fun objId => toAVM (next objId))
  | .destroy cid destrId selfId args next =>
    .destructor cid destrId selfId args (toAVM next)
  | .call cid methodId selfId args next =>
    .method cid methodId selfId args (toAVM next)
  | @fetch _ _ _ i objId next =>
    .fetch ⟨i.classId.label, objId⟩ (fun obj => toAVM (next (i.fromObject obj.data)))
  | .return val =>
    .return val

def Program.map {lab : Ecosystem.Label} {A B : Type} (f : A → B) (prog : Program lab A) : Program lab B :=
  match prog with
  | .create C cid constrId args next =>
    .create C cid constrId args (fun x => map f (next x))
  | .destroy cid destrId selfId args next =>
    .destroy cid destrId selfId args (map f next)
  | .call cid methodId selfId args next =>
    .call cid methodId selfId args (map f next)
  | @fetch _ _ C _ objId next =>
    .fetch C objId (fun x => map f (next x))
  | .return val =>
    .return (f val)

def Program.create' {ReturnType} (C : Type) [i : IsObject C] (constrId : i.classId.label.ConstructorId) (args : constrId.Args.type) (next : Reference C → Program i.label ReturnType) : Program i.label ReturnType :=
  Program.create C i.classId constrId args (fun objId => next ⟨objId⟩)

def Program.destroy' {ReturnType} {C : Type} (r : Reference C) [i : IsObject C] (destrId : i.classId.label.DestructorId) (args : destrId.Args.type) (next : Program i.label ReturnType) : Program i.label ReturnType :=
  Program.destroy i.classId destrId r.objId args next

def Program.call' {ReturnType} {C : Type} (r : Reference C) [i : IsObject C] (methodId : i.classId.label.MethodId) (args : methodId.Args.type) (next : Program i.label ReturnType) : Program i.label ReturnType :=
  Program.call i.classId methodId r.objId args next

def Program.fetch' {ReturnType} {lab : Ecosystem.Label} {C : Type} (r : Reference C) [i : IsObject C] (next : C → Program lab ReturnType) : Program lab ReturnType :=
  Program.fetch C r.objId next
