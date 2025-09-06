import AVM.Object
import AVM.Class.Label
import AVM.Ecosystem.Label
import AVM.Program.Parameters

namespace AVM

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

def Program.invoke
    {α β : Type u}
    {lab : Ecosystem.Label}
    (prog : Program lab α)
    (next : α → Program lab β)
    : Program lab β :=
  match prog with
  | .constructor cid constrId args cont =>
    .constructor cid constrId args (fun objId => Program.invoke (cont objId) next)
  | .destructor cid destrId selfId args cont =>
    .destructor cid destrId selfId args (Program.invoke cont next)
  | .method cid methodId selfId args cont =>
    .method cid methodId selfId args (Program.invoke cont next)
  | .fetch objId cont =>
    .fetch objId (fun obj => Program.invoke (cont obj) next)
  | .return val =>
    next val

/-- All body parameters - the parameters at the point of the return statement.
  This does not include the parameters of the called methods / constructors /
  destructors. -/
def Program.params {lab ReturnType} (prog : Program lab ReturnType) : Program.Parameters :=
  match prog with
  | .constructor _ _ _ next =>
    .genId (fun newId => next newId |>.params)
  | .destructor _ _ _ _ next => next.params
  | .method _ _ _ _ next => next.params
  | .fetch objId next =>
    .fetch objId (fun obj => next obj |>.params)
  | .return _ => .empty

def Program.returnValue {lab ReturnType} (prog : Program lab ReturnType) (vals : prog.params.Product) : ReturnType :=
  match prog, vals with
  | .constructor _ _ _ next, ⟨newId, vals'⟩ =>
    next newId |>.returnValue vals'
  | .destructor _ _ _ _ next, vals' =>
    next.returnValue vals'
  | .method _ _ _ _ next, vals' =>
    next.returnValue vals'
  | .fetch _ next, ⟨obj, vals'⟩ =>
    next obj |>.returnValue vals'
  | .return val, () => val
