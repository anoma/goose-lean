import AVM
import Applib.Surface.Object
import Applib.Surface.Reference

namespace Applib

open AVM

inductive Program.Parameters where
  | empty
  | fetch (C : Type) (i : IsObject C) (param : ObjectId) (rest : C → Program.Parameters)
  | genId (rest : ObjectId → Program.Parameters)
deriving Inhabited

def Program.Parameters.Product : Program.Parameters → Type
  | .empty => Unit
  | .fetch C _ _ rest => Σ (c : C), (rest c).Product
  | .genId rest => Σ (id : ObjectId), (rest id).Product

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
  | .genId ps1 =>
    .genId (fun objId => (ps1 objId).append (fun vals => params2 ⟨objId, vals⟩))

def Program.Parameters.snocFetch (C : Type) [i : IsObject C] (params : Program.Parameters) (objId : params.Product → ObjectId) : Program.Parameters :=
  params.append (fun vals => .fetch C i (objId vals) (fun _ => .empty))

def Program.Parameters.snocGenId (params : Program.Parameters) : Program.Parameters :=
  params.append (fun _ => .genId (fun _ => .empty))

def Program.Parameters.toTaskParameters : Program.Parameters → Task.Parameters
  | .empty => .empty
  | .fetch _ i p rest => .fetch ⟨i.classId.label, p⟩ (fun obj => toTaskParameters (rest (i.fromObject obj.data)))
  | .genId rest => .genId (fun id => toTaskParameters (rest id))

def Task.Parameters.Values.toProgramParameterValues {params : Program.Parameters} (vals : params.toTaskParameters.Product) : params.Product :=
  match params with
  | .empty => ()
  | .fetch _ i _ _ =>
    let ⟨obj, vals'⟩ := vals
    ⟨i.fromObject obj.data, toProgramParameterValues vals'⟩
  | .genId _ =>
    let ⟨objId, vals'⟩ := vals
    ⟨objId, toProgramParameterValues vals'⟩

lemma Program.Parameters.toTaskParameters_genId {params : Program.Parameters} :
  params.snocGenId.toTaskParameters = params.toTaskParameters.snocGenId := by
  induction params <;> simp [Program.Parameters.snocGenId, Program.Parameters.toTaskParameters, Program.Parameters.append]
  case fetch C i p1 ps1 ih => congr; funext; apply ih
  case genId ps1 ih => congr; funext; apply ih
  case empty => rfl

lemma Program.Parameters.toTaskParameters_snocFetch (C : Type) [i : IsObject C] {params : Program.Parameters} (objId : params.Product → ObjectId) :
  (params.snocFetch C objId).toTaskParameters =
    params.toTaskParameters.snocFetch (fun vals => ⟨i.classId.label, objId (Task.Parameters.Values.toProgramParameterValues vals)⟩) := by
  induction params <;> simp [Program.Parameters.snocFetch, Program.Parameters.toTaskParameters, Program.Parameters.append]
  case fetch C' i' p1 ps1 ih => congr; funext; apply ih
  case genId ps1 ih => congr; funext; apply ih
  case empty => rfl

inductive Program' (lab : Ecosystem.Label) (ReturnType : Type) : Program.Parameters → Type 2 where
  | create
      {params : Program.Parameters}
      (cid : lab.ClassId)
      (constrId : cid.label.ConstructorId)
      (args : params.Product → constrId.Args.type)
      (next : Program' lab ReturnType params.snocGenId)
      : Program' lab ReturnType params
  | destroy
      {params : Program.Parameters}
      (cid : lab.ClassId)
      (destrId : cid.label.DestructorId)
      (selfId : params.Product → ObjectId)
      (args : params.Product → destrId.Args.type)
      (next : Program' lab ReturnType params)
      : Program' lab ReturnType params
  | call
      {params : Program.Parameters}
      (cid : lab.ClassId)
      (methodId : cid.label.MethodId)
      (selfId : params.Product → ObjectId)
      (args : params.Product → methodId.Args.type)
      (next : Program' lab ReturnType params)
      : Program' lab ReturnType params
  | fetch
      {params : Program.Parameters}
      (C : Type)
      [i : IsObject C]
      (objId : params.Product → ObjectId)
      (next : Program' lab ReturnType (params.snocFetch C objId))
      : Program' lab ReturnType params
  | return
      {params : Program.Parameters}
      (val : params.Product → ReturnType)
      : Program' lab ReturnType params

def Program'.toBody {lab ReturnType params} (prog : Program' lab ReturnType params) : Class.Member.Body lab ReturnType params.toTaskParameters :=
  match prog with
  | .create cid constrId args next =>
    let next' := cast (by rw [Program.Parameters.toTaskParameters_genId]) (toBody next)
    .constructor cid constrId (convertFun args) next'
  | .destroy cid destrId selfId args next =>
    .destructor cid destrId (convertFun selfId) (convertFun args) (toBody next)
  | .call cid methodId selfId args next =>
    .method cid methodId (convertFun selfId) (convertFun args) (toBody next)
  | @fetch _ _ _ C i objId next =>
    let next' := cast (by rw [Program.Parameters.toTaskParameters_snocFetch C objId]) (toBody next)
    .fetch (fun vals => ⟨i.classId.label, objId (Task.Parameters.Values.toProgramParameterValues vals)⟩) next'
  | .return val =>
    .return (convertFun val)
  where
    convertFun {A} {params : Program.Parameters} (f : params.Product → A) (vals : params.toTaskParameters.Product) : A :=
      f (Task.Parameters.Values.toProgramParameterValues vals)

def Program'.map {lab : Ecosystem.Label} {A B : Type} {params : Program.Parameters} (f : A → B) (prog : Program' lab A params) : Program' lab B params :=
  match prog with
  | .create cid constrId args next =>
    .create cid constrId args (map f next)
  | .destroy cid destrId selfId args next =>
    .destroy cid destrId selfId args (map f next)
  | .call cid methodId selfId args next =>
    .call cid methodId selfId args (map f next)
  | @fetch _ _ _ C _ objId next =>
    .fetch C objId (map f next)
  | .return val =>
    .return (f ∘ val)

def Program (lab : Ecosystem.Label) (Result : Type) := Program' lab Result .empty

def Program.map {lab : Ecosystem.Label} {A B : Type} (f : A → B) (prog : Program lab A) : Program lab B := Program'.map f prog

alias Program.create := Program'.create
alias Program.destroyById := Program'.destroy
alias Program.callById := Program'.call
alias Program.fetchById := Program'.fetch
alias Program.return := Program'.return

def Program.destroy {params ReturnType} (C : Type) [i : IsObject C] (destrId : i.classId.label.DestructorId) (r : params.Product → Reference C) (args : params.Product → destrId.Args.type) (next : Program' i.label ReturnType params) : Program' i.label ReturnType params :=
  Program.destroyById i.classId destrId (fun vals => (r vals).objId) args next

def Program.call {params ReturnType} (C : Type) [i : IsObject C] (methodId : i.classId.label.MethodId) (r : params.Product → Reference C) (args : params.Product → methodId.Args.type) (next : Program' i.label ReturnType params) : Program' i.label ReturnType params :=
  Program.callById i.classId methodId (fun vals => (r vals).objId) args next

def Program.fetch {params ReturnType} {lab : Ecosystem.Label} {C : Type} (r : params.Product → Reference C) [i : IsObject C] (next : Program' lab ReturnType (params.snocFetch C (fun vals => (r vals).objId))) : Program' lab ReturnType params :=
  Program.fetchById C (fun vals => (r vals).objId) next
