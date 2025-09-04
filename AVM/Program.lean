import AVM.Object
import AVM.Class.Label
import AVM.Ecosystem.Label
import AVM.Program.Parameters

namespace AVM

/-- The parameters `params` represent objects fetched and new object ids
  generated in the body before the current statement. -/
inductive Program'.{u} (lab : Ecosystem.Label) : (ReturnType : Type u) → Nat → Type (u + 1) where
  | constructor
    {ReturnType : Type u}
    {n : Nat}
    (cid : lab.ClassId)
    (constrId : cid.label.ConstructorId)
    (args : constrId.Args.type)
    (next : ObjectId → Program' lab ReturnType n)
    : Program' lab ReturnType (n + 1)
  | destructor
    {ReturnType : Type u}
    {n : Nat}
    (cid : lab.ClassId)
    (destrId : cid.label.DestructorId)
    (selfId : ObjectId)
    (args : destrId.Args.type)
    (next : Program' lab ReturnType n)
    : Program' lab ReturnType (n + 1)
  | method
    {ReturnType : Type u}
    {n : Nat}
    (cid : lab.ClassId)
    (methodId : cid.label.MethodId)
    (selfId : ObjectId)
    (args : methodId.Args.type)
    (next : Program' lab ReturnType n)
    : Program' lab ReturnType (n + 1)
  | fetch
    {ReturnType : Type u}
    {n : Nat}
    (objId : TypedObjectId)
    (next : Object objId.classLabel → Program' lab ReturnType n)
    : Program' lab ReturnType (n + 1)
  | invoke
    {ReturnType α : Type u}
    {n : Nat}
    (i : Inhabited α)
    (prog : Program' lab α n)
    (next : α → Program' lab ReturnType n)
    : Program' lab ReturnType (n + 1)
  | return
    {ReturnType : Type u}
    {n : Nat}
    (val : ReturnType)
    : Program' lab ReturnType n

instance (ReturnType : Type u) [Inhabited ReturnType] :
    Inhabited (Σ (params : Program.Parameters), params.Product → ReturnType) :=
  ⟨⟨.empty, fun _ => default⟩⟩

def Program lab ReturnType := Σ n, Program' lab ReturnType n

def Program'.result {lab : Ecosystem.Label} {ReturnType} {n : Nat} (prog : Program' lab ReturnType n)
  : Σ (params : Program.Parameters), params.Product → ReturnType :=
  match n, prog with
  | Nat.succ z, .constructor _ _ _ next =>
    ⟨.genId (fun objId => result (n := z) (next objId) |>.1),
      fun ⟨objId, vals⟩ => result (n := z) (next objId) |>.2 vals⟩
  | Nat.succ m, .destructor _ _ _ _ next => next.result (n := m)
  | Nat.succ m, .method _ _ _ _ next => next.result (n := m)
  | Nat.succ m, .fetch objId next =>
    ⟨.fetch objId (fun obj => result (n := m) (next obj) |>.1),
      fun ⟨obj, vals⟩ => result (n := m) (next obj) |>.2 vals⟩
  | Nat.succ m, .invoke _ p next =>
    let ⟨pParams, pReturn⟩ := p.result (n := m)
    let params :=
      pParams.append (fun pVals =>
        result (n := m) (next (pReturn pVals)) |>.1)
    ⟨params, fun vals =>
      let ⟨pVals, vals'⟩ := Program.Parameters.splitProduct vals
      result (n := m) (next (pReturn pVals)) |>.2 vals'⟩
  | _, .return val => ⟨.empty, fun () => val⟩


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
