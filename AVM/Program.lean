import AVM.Object
import AVM.Class.Label
import AVM.Ecosystem.Label
import AVM.Program.Parameters

namespace AVM

/-- The parameters `params` represent objects fetched and new object ids
  generated in the body before the current statement. -/
inductive Program.{u} (lab : Ecosystem.Label) : (ReturnType : Type u) → Type (u + 1) where
  | constructor
    {ReturnType : Type u}
    (cid : lab.ClassId)
    (constrId : cid.label.ConstructorId)
    (args : constrId.Args.type)
    (next : ObjectId → Program lab ReturnType)
    : Program lab ReturnType
  | destructor
    {ReturnType : Type u}
    (cid : lab.ClassId)
    (destrId : cid.label.DestructorId)
    (selfId : ObjectId)
    (args : destrId.Args.type)
    (next : Program lab ReturnType)
    : Program lab ReturnType
  | method
    {ReturnType : Type u}
    (cid : lab.ClassId)
    (methodId : cid.label.MethodId)
    (selfId : ObjectId)
    (args : methodId.Args.type)
    (next : Program lab ReturnType)
    : Program lab ReturnType
  | fetch
    {ReturnType : Type u}
    (objId : TypedObjectId)
    (next : Object objId.classLabel → Program lab ReturnType)
    : Program lab ReturnType
  | invoke
    {ReturnType α : Type u}
    (i : Inhabited α)
    (prog : Program lab α)
    (next : α → Program lab ReturnType)
    : Program lab ReturnType
  | return
    {ReturnType : Type u}
    (val : ReturnType)
    : Program lab ReturnType

instance (ReturnType : Type u) [Inhabited ReturnType] :
    Inhabited (Σ (params : Program.Parameters), params.Product → ReturnType) :=
  ⟨⟨.empty, fun _ => default⟩⟩

def Program.result {ReturnType} [Inhabited ReturnType] (lab : Ecosystem.Label) (prog : Program lab ReturnType)
  : Σ (params : Program.Parameters), params.Product → ReturnType :=
  match prog with
  | .constructor _ _ _ next =>
    ⟨.genId (fun objId => Program.result lab (next objId) |>.1),
      fun ⟨objId, vals⟩ => Program.result lab (next objId) |>.2 vals⟩
  | .destructor _ _ _ _ next => next.result
  | .method _ _ _ _ next => next.result
  | .fetch objId next =>
    ⟨.fetch objId (fun obj => Program.result lab (next obj) |>.1),
      fun ⟨obj, vals⟩ => Program.result lab (next obj) |>.2 vals⟩
  | .invoke _ p next =>
    let ⟨pParams, pReturn⟩ := p.result
    let params :=
      pParams.append (fun pVals =>
        Program.result lab (next (pReturn pVals)) |>.1)
    ⟨params, fun vals =>
      let ⟨pVals, vals'⟩ := Program.Parameters.splitProduct vals
      Program.result lab (next (pReturn pVals)) |>.2 vals'⟩
  | .return val => ⟨.empty, fun () => val⟩

/-- All body parameters - the parameters at the point of the return statement. -/
def Program.params {lab ReturnType} [Inhabited ReturnType] (prog : Program lab ReturnType) : Program.Parameters :=
  prog.result.1

def Program.returnValue {lab ReturnType} [Inhabited ReturnType] (prog : Program lab ReturnType) (vals : prog.params.Product) : ReturnType :=
  prog.result.2 vals

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
  | .invoke i p next =>
    .invoke i p (fun x => map f (next x))
  | .return val =>
    .return (f val)
