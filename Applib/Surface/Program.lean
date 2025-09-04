import AVM
import Applib.Surface.Object
import Applib.Surface.Reference

namespace Applib

open AVM

inductive Program.Parameters where
  | empty
  | fetch (C : Type) (i : IsObject C) (param : ObjectId) (rest : C → Program.Parameters)
  | genRef (C : Type) (rest : Reference C → Program.Parameters)
deriving Inhabited

def Program.Parameters.Product : Program.Parameters → Type
  | .empty => Unit
  | .fetch C _ _ rest => Σ (c : C), (rest c).Product
  | .genRef C rest => Σ (ref : Reference C), (rest ref).Product

def Program.Parameters.append (params1 : Program.Parameters) (params2 : params1.Product → Program.Parameters) : Program.Parameters :=
  match params1 with
  | .empty =>
    params2 ()
  | .fetch C i p1 ps1 =>
    .fetch C i p1
      (fun obj =>
        (ps1 obj).append
          (fun vals =>
            params2 ⟨obj, vals⟩))
  | .genRef C ps1 =>
    .genRef C (fun ref => (ps1 ref).append (fun vals => params2 ⟨ref, vals⟩))

def Program.Parameters.snocFetch (C : Type) [i : IsObject C] (params : Program.Parameters) (objId : params.Product → ObjectId) : Program.Parameters :=
  params.append (fun vals => .fetch C i (objId vals) (fun _ => .empty))

def Program.Parameters.snocGenId (C : Type) (params : Program.Parameters) : Program.Parameters :=
  params.append (fun _ => .genRef C (fun _ => .empty))

def Program.Parameters.toTaskParameters : Program.Parameters → Task.Parameters
  | .empty => .empty
  | .fetch _ i p rest => .fetch ⟨i.classId.label, p⟩ (fun obj => toTaskParameters (rest (i.fromObject obj.data)))
  | .genRef _ rest => .genId (fun id => toTaskParameters (rest ⟨id⟩))

def Task.Parameters.Values.toProgramParameterValues {params : Program.Parameters} (vals : params.toTaskParameters.Product) : params.Product :=
  match params with
  | .empty => ()
  | .fetch _ i _ _ =>
    let ⟨obj, vals'⟩ := vals
    ⟨i.fromObject obj.data, toProgramParameterValues vals'⟩
  | .genRef _ _ =>
    let ⟨objId, vals'⟩ := vals
    ⟨⟨objId⟩, toProgramParameterValues vals'⟩

lemma Program.Parameters.toTaskParameters_genId {params : Program.Parameters} (C : Type) :
  (params.snocGenId C).toTaskParameters = params.toTaskParameters.snocGenId := by
  induction params <;> simp [Program.Parameters.snocGenId, Program.Parameters.toTaskParameters, Program.Parameters.append]
  case fetch C' i p1 ps1 ih => congr; funext; apply ih
  case genRef C' ps1 ih => congr; funext; apply ih
  case empty => rfl

lemma Program.Parameters.toTaskParameters_snocFetch (C : Type) [i : IsObject C] {params : Program.Parameters} (objId : params.Product → ObjectId) :
  (params.snocFetch C objId).toTaskParameters =
    params.toTaskParameters.snocFetch (fun vals => ⟨i.classId.label, objId (Task.Parameters.Values.toProgramParameterValues vals)⟩) := by
  induction params <;> simp [Program.Parameters.snocFetch, Program.Parameters.toTaskParameters, Program.Parameters.append]
  case fetch C' i' p1 ps1 ih => congr; funext; apply ih
  case genRef C' ps1 ih => congr; funext; apply ih
  case empty => rfl

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

def Program.destroy' {ReturnType} (C : Type) [i : IsObject C] (destrId : i.classId.label.DestructorId) (r : Reference C) (args : destrId.Args.type) (next : Program i.label ReturnType) : Program i.label ReturnType :=
  Program.destroy i.classId destrId r.objId args next

def Program.call' {ReturnType} (C : Type) [i : IsObject C] (methodId : i.classId.label.MethodId) (r : Reference C) (args : methodId.Args.type) (next : Program i.label ReturnType) : Program i.label ReturnType :=
  Program.call i.classId methodId r.objId args next

def Program.fetch' {ReturnType} {lab : Ecosystem.Label} {C : Type} (r : Reference C) [i : IsObject C] (next : C → Program lab ReturnType) : Program lab ReturnType :=
  Program.fetch C r.objId next
