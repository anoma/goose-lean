import AVM.Object
import AVM.Class.Label
import AVM.Ecosystem.Label
import AVM.Program.Parameters

namespace AVM

/-- The parameters `params` represent objects fetched and new object ids
  generated in the body before the current statement. -/
inductive Program.{u} (lab : Ecosystem.Label) (ReturnType : Type u) : Type (u + 1) where
  | constructor
      (cid : lab.ClassId)
      (constrId : cid.label.ConstructorId)
      (args : constrId.Args.type)
      (next : ObjectId → Program lab ReturnType)
      : Program lab ReturnType
  | destructor
      (cid : lab.ClassId)
      (destrId : cid.label.DestructorId)
      (selfId : ObjectId)
      (args : destrId.Args.type)
      (next : Program lab ReturnType)
      : Program lab ReturnType
  | method
      (cid : lab.ClassId)
      (methodId : cid.label.MethodId)
      (selfId : ObjectId)
      (args : methodId.Args.type)
      (next : Program lab ReturnType)
      : Program lab ReturnType
  | fetch
      (objId : TypedObjectId)
      (next : Object objId.classLabel → Program lab ReturnType)
      : Program lab ReturnType
  | return
      (val : ReturnType)
      : Program lab ReturnType

/-- All body parameters - the parameters at the point of the return statement. -/
def Program.params {lab ReturnType} (prog : Program lab ReturnType) : Program.Parameters :=
  match prog with
  | .constructor _ _ _ next => .genId (fun objId => next objId |>.params)
  | .destructor _ _ _ _ next => next.params
  | .method _ _ _ _ next => next.params
  | .fetch objId next => .fetch objId (fun obj => next obj |>.params)
  | .return _ => .empty

def Program.returnValue {lab ReturnType} (prog : Program lab ReturnType) (vals : prog.params.Product) : ReturnType :=
  match prog with
  | .constructor _ _ _ next =>
    let ⟨newId, vals'⟩ := vals
    next newId |>.returnValue vals'
  | .destructor _ _ _ _ next => next.returnValue vals
  | .method _ _ _ _ next => next.returnValue vals
  | .fetch _ next =>
    let ⟨obj, vals'⟩ := vals
    next obj |>.returnValue vals'
  | .return val => val

def Program.map {lab : Ecosystem.Label} {A B : Type u} (f : A → B) (prog : Program lab A) : Program lab B :=
  match prog with
  | .constructor cid constrId args next =>
    .constructor cid constrId args (fun x => map f (next x))
  | .destructor cid destrId selfId args next =>
    .destructor cid destrId selfId args (map f next)
  | .method cid methodId selfId args next =>
    .method cid methodId selfId args (map f next)
  | .fetch objId next =>
    .fetch objId (fun x => map f (next x))
  | .return val =>
    .return (f val)
