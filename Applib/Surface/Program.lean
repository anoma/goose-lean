import AVM
import Applib.Surface.Object
import Applib.Surface.Reference

namespace Applib

open AVM

inductive Program (lab : Scope.Label) : (α : Type u) → Type (u + 1) where
  | create
    {α : Type u}
    (eid : lab.EcosystemId)
    (cid : eid.label.ClassId)
    (constrId : cid.label.ConstructorId)
    (args : constrId.Args.type)
    (signatures : constrId.Signatures args)
    (next : ObjectId → Program lab α)
    : Program lab α
  | destroy
    {α : Type u}
    (eid : lab.EcosystemId)
    (cid : eid.label.ClassId)
    (destrId : cid.label.DestructorId)
    (selfId : ObjectId)
    (args : destrId.Args.type)
    (signatures : destrId.Signatures args)
    (next : Program lab α)
    : Program lab α
  | call
    {α : Type u}
    (eid : lab.EcosystemId)
    (cid : eid.label.ClassId)
    (methodId : cid.label.MethodId)
    (selfId : ObjectId)
    (args : methodId.Args.type)
    (signatures : methodId.Signatures args)
    (next : Program lab α)
    : Program lab α
  | multiCall
    {α : Type u}
    (eid : lab.EcosystemId)
    (multiId : eid.label.MultiMethodId)
    (selves : multiId.SelvesIds)
    (args : multiId.Args.type)
    (signatures : multiId.Signatures args)
    (next : Program lab α)
    : Program lab α
  | upgrade
    {α : Type u}
    (eid : lab.EcosystemId)
    (classId : eid.label.ClassId)
    (selfId : ObjectId)
    (objData : SomeObjectData)
    (next : Program lab α)
    : Program lab α
  | fetch
    {α : Type u}
    (C : Type)
    [i : IsObject C]
    (objId : ObjectId)
    (next : C → Program lab α)
    : Program lab α
  | invoke
    {α β : Type u}
    (prog : Program lab β)
    (next : β → Program lab α)
    : Program lab α
  | return
    {α : Type u}
    (val : α)
    : Program lab α

def Program.toAVM {lab : Scope.Label} {α} (prog : Program lab α) : AVM.Program lab α :=
  match prog with
  | .create eid cid constrId args signatures next =>
    .constructor eid cid constrId args signatures (fun objId => toAVM (next objId))
  | .destroy eid cid destrId selfId args signatures next =>
    .destructor eid cid destrId selfId args signatures (toAVM next)
  | .call eid cid methodId selfId args signatures next =>
    .method eid cid methodId selfId args signatures (toAVM next)
  | .multiCall eid multiId selves args signatures next =>
    .multiMethod eid multiId selves args signatures (toAVM next)
  | .upgrade eid classId selfId obj next =>
    .upgrade eid classId selfId obj (toAVM next)
  | @fetch _ _ _ i objId next =>
    .fetch (classId := i.classId) objId (fun obj => toAVM (next (i.fromObject obj.data)))
  | .invoke p next =>
    .invoke (toAVM p) (fun x => toAVM (next x))
  | .return val =>
    .return val

def Program.map {lab : Scope.Label} {A B : Type} (f : A → B) (prog : Program lab A) : Program lab B :=
  match prog with
  | .create eid cid constrId args signatures next =>
    .create eid cid constrId args signatures (fun x => map f (next x))
  | .destroy eid cid destrId selfId args signatures next =>
    .destroy eid cid destrId selfId args signatures (map f next)
  | .call eid cid methodId selfId args signatures next =>
    .call eid cid methodId selfId args signatures (map f next)
  | .multiCall eid multiId selvesIds args signatures next =>
    .multiCall eid multiId selvesIds args signatures (map f next)
  | .upgrade eid classId selfId obj next =>
    .upgrade eid classId selfId obj (map f next)
  | @fetch _ _ C _ objId next =>
    .fetch C objId (fun x => map f (next x))
  | .invoke p next =>
    .invoke p (fun x => map f (next x))
  | .return val =>
    .return (f val)

def Program.create'
  {α}
  {lab : Scope.Label}
  (C : Type)
  [i : IsObject C]
  (inScope : i.label ∈ lab)
  (constrId : i.classId.label.ConstructorId)
  (args : constrId.Args.type)
  (signatures : constrId.Signatures args)
  (next : Reference C → Program lab α)
  : Program lab α :=
  let ⟨eid, _⟩ := inScope
  Program.create
    eid
    (cast (by grind) i.classId)
    (cast (by grind) constrId)
    (cast (by grind) args)
    (cast (by grind) signatures)
    (fun objId => next ⟨objId⟩)

def Program.destroy'
  {α}
  {lab : Scope.Label}
  {C : Type}
  (r : Reference C)
  [i : IsObject C]
  (inScope : i.label ∈ lab)
  (destrId : i.classId.label.DestructorId)
  (args : destrId.Args.type)
  (signatures : destrId.Signatures args)
  (next : Program lab α)
  : Program lab α :=
  let ⟨eid, _⟩ := inScope
  Program.destroy
    eid
    (cast (by grind) i.classId)
    (cast (by grind) destrId)
    r.objId
    (cast (by grind) args)
    (cast (by grind) signatures)
    next

def Program.call'
  {α}
  {C : Type}
  {lab : Scope.Label}
  (r : Reference C)
  [i : IsObject C]
  (inScope : i.label ∈ lab)
  (methodId : i.classId.label.MethodId)
  (args : methodId.Args.type)
  (signatures : methodId.Signatures args)
  (next : Program lab α)
  : Program lab α :=
  let ⟨eid, _⟩ := inScope
  Program.call
    eid
    (cast (by grind) i.classId)
    (cast (by grind) methodId)
    r.objId
    (cast (by grind) args)
    (cast (by grind) signatures)
    next

def Program.upgrade'
  {α}
  {C C' : Type}
  {lab : Scope.Label}
  (r : Reference C)
  [i : IsObject C]
  [i' : IsObject C']
  (inScope : i.label ∈ lab)
  (c' : C')
  (next : Program lab α)
  : Program lab α := by
  rcases inScope with ⟨eid, _⟩
  refine Program.upgrade eid ?_ r.objId (i'.toObject c' |>.toSomeObjectData) next
  exact cast (by grind) i.classId;

def Program.multiCall'
  {α}
  {lab : Scope.Label}
  {eid : lab.EcosystemId}
  (multiId : eid.label.MultiMethodId)
  (selves : multiId.SelvesReferences)
  (args : multiId.Args.type)
  (signatures : multiId.Signatures args)
  (next : Program lab α)
  : Program lab α :=
  let selves' : multiId.SelvesIds := fun x => selves x |>.ref.objId
  multiCall eid multiId selves' args signatures next

def Program.fetch'
  {α}
  {lab : Scope.Label}
  {C : Type}
  (r : Reference C)
  [i : IsObject C]
  (next : C → Program lab α)
  : Program lab α :=
  Program.fetch C r.objId next
