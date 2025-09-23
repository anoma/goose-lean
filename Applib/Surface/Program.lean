import AVM
import Applib.Surface.Object
import Applib.Surface.Reference

namespace Applib

open AVM

inductive Program (lab : Ecosystem.Label) : (ReturnType : Type u) → Type (u + 1) where
  | create
    {ReturnType : Type u}
    (C : Type)
    (cid : lab.ClassId)
    (constrId : cid.label.ConstructorId)
    (args : constrId.Args.type)
    (signatures : constrId.Signatures args)
    (next : ObjectId → Program lab ReturnType)
    : Program lab ReturnType
  | destroy
    {ReturnType : Type u}
    (cid : lab.ClassId)
    (destrId : cid.label.DestructorId)
    (selfId : ObjectId)
    (args : destrId.Args.type)
    (signatures : destrId.Signatures args)
    (next : Program lab ReturnType)
    : Program lab ReturnType
  | call
    {ReturnType : Type u}
    (cid : lab.ClassId)
    (methodId : cid.label.MethodId)
    (selfId : ObjectId)
    (args : methodId.Args.type)
    (signatures : methodId.Signatures args)
    (next : Program lab ReturnType)
    : Program lab ReturnType
  | multiCall
    {ReturnType : Type u}
    (multiId : lab.MultiMethodId)
    (selves : multiId.SelvesIds)
    (args : multiId.Args.type)
    (signatures : multiId.Signatures args)
    (next : Program lab ReturnType)
    : Program lab ReturnType
  | upgrade
    {ReturnType : Type u}
    (classId : lab.ClassId)
    (selfId : ObjectId)
    (objData : SomeObjectData)
    (next : Program lab ReturnType)
    : Program lab ReturnType
  | fetch
    {ReturnType : Type u}
    (C : Type)
    [i : IsObject C]
    (objId : ObjectId)
    (next : C → Program lab ReturnType)
    : Program lab ReturnType
  | invoke
    {ReturnType : Type u}
    {α : Type u}
    (prog : Program lab α)
    (next : α → Program lab ReturnType)
    : Program lab ReturnType
  | return
    {ReturnType : Type u}
    (val : ReturnType)
    : Program lab ReturnType

def Program.toAVM {lab ReturnType} (prog : Program lab ReturnType) : AVM.Program lab ReturnType :=
  match prog with
  | .create _ cid constrId args signatures next =>
    .constructor cid constrId args signatures (fun objId => toAVM (next objId))
  | .destroy cid destrId selfId args signatures next =>
    .destructor cid destrId selfId args signatures (toAVM next)
  | .call cid methodId selfId args signatures next =>
    .method cid methodId selfId args signatures (toAVM next)
  | .multiCall multiId selves args signatures next =>
    .multiMethod multiId selves args signatures (toAVM next)
  | .upgrade classId selfId obj next =>
    .upgrade classId selfId obj (toAVM next)
  | @fetch _ _ _ i objId next =>
    .fetch (classId := i.classId) objId (fun obj => toAVM (next (i.fromObject obj.data)))
  | .invoke p next =>
    .invoke (toAVM p) (fun x => toAVM (next x))
  | .return val =>
    .return val

def Program.map {lab : Ecosystem.Label} {A B : Type} (f : A → B) (prog : Program lab A) : Program lab B :=
  match prog with
  | .create C cid constrId args signatures next =>
    .create C cid constrId args signatures (fun x => map f (next x))
  | .destroy cid destrId selfId args signatures next =>
    .destroy cid destrId selfId args signatures (map f next)
  | .call cid methodId selfId args signatures next =>
    .call cid methodId selfId args signatures (map f next)
  | .multiCall multiId selvesIds args signatures next =>
    .multiCall multiId selvesIds args signatures (map f next)
  | .upgrade classId selfId obj next =>
    .upgrade classId selfId obj (map f next)
  | @fetch _ _ C _ objId next =>
    .fetch C objId (fun x => map f (next x))
  | .invoke p next =>
    .invoke p (fun x => map f (next x))
  | .return val =>
    .return (f val)

def Program.create'
  {ReturnType}
  (C : Type)
  [i : IsObject C]
  (constrId : i.classId.label.ConstructorId)
  (args : constrId.Args.type)
  (signatures : constrId.Signatures args)
  (next : Reference C → Program i.label ReturnType)
  : Program i.label ReturnType :=
  Program.create C i.classId constrId args signatures (fun objId => next ⟨objId⟩)

def Program.destroy'
  {ReturnType}
  {C : Type}
  (r : Reference C)
  [i : IsObject C]
  (destrId : i.classId.label.DestructorId)
  (args : destrId.Args.type)
  (signatures : destrId.Signatures args)
  (next : Program i.label ReturnType)
  : Program i.label ReturnType :=
  Program.destroy i.classId destrId r.objId args signatures next

def Program.call'
  {ReturnType}
  {C : Type}
  (r : Reference C)
  [i : IsObject C]
  (methodId : i.classId.label.MethodId)
  (args : methodId.Args.type)
  (signatures : methodId.Signatures args)
  (next : Program i.label ReturnType)
  : Program i.label ReturnType :=
  Program.call i.classId methodId r.objId args signatures next

def Program.upgrade'
  {ReturnType}
  {C C' : Type}
  (r : Reference C)
  [i : IsObject C]
  [i' : IsObject C']
  (c' : C')
  (next : Program i.label ReturnType)
  : Program i.label ReturnType :=
  Program.upgrade i.classId r.objId (i'.toObject c' |>.toSomeObjectData) next

def Program.multiCall'
  {α}
  {lab : Ecosystem.Label}
  (multiId : lab.MultiMethodId)
  (selves : multiId.SelvesReferences)
  (args : multiId.Args.type)
  (signatures : multiId.Signatures args)
  (next : Program lab α)
  : Program lab α :=
  let selves' : multiId.SelvesIds := fun x => selves x |>.ref.objId
  multiCall multiId selves' args signatures next

def Program.fetch' {ReturnType} {lab : Ecosystem.Label} {C : Type} (r : Reference C) [i : IsObject C] (next : C → Program lab ReturnType) : Program lab ReturnType :=
  Program.fetch C r.objId next
