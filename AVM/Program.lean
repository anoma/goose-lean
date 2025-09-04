import AVM.Object
import AVM.Class.Label
import AVM.Ecosystem.Label
import AVM.Program.Parameters

namespace AVM

inductive Program.Sized.{u} (lab : Ecosystem.Label) : (ReturnType : Type u) → Nat → Type (u + 1) where
  | constructor
    {ReturnType : Type u}
    {n : Nat}
    (cid : lab.ClassId)
    (constrId : cid.label.ConstructorId)
    (args : constrId.Args.type)
    (next : ObjectId → Program.Sized lab ReturnType n)
    : Program.Sized lab ReturnType (n + 1)
  | destructor
    {ReturnType : Type u}
    {n : Nat}
    (cid : lab.ClassId)
    (destrId : cid.label.DestructorId)
    (selfId : ObjectId)
    (args : destrId.Args.type)
    (next : Program.Sized lab ReturnType n)
    : Program.Sized lab ReturnType (n + 1)
  | method
    {ReturnType : Type u}
    {n : Nat}
    (cid : lab.ClassId)
    (methodId : cid.label.MethodId)
    (selfId : ObjectId)
    (args : methodId.Args.type)
    (next : Program.Sized lab ReturnType n)
    : Program.Sized lab ReturnType (n + 1)
  | fetch
    {ReturnType : Type u}
    {n : Nat}
    (objId : TypedObjectId)
    (next : Object objId.classLabel → Program.Sized lab ReturnType n)
    : Program.Sized lab ReturnType (n + 1)
  | invoke
    {ReturnType α : Type u}
    {n : Nat}
    (prog : Program.Sized lab α n)
    (next : α → Program.Sized lab ReturnType n)
    : Program.Sized lab ReturnType (n + 1)
  | return
    {ReturnType : Type u}
    {n : Nat}
    (val : ReturnType)
    : Program.Sized lab ReturnType n

instance (ReturnType : Type u) [Inhabited ReturnType] :
    Inhabited (Σ (params : Program.Parameters), params.Product → ReturnType) :=
  ⟨⟨.empty, fun _ => default⟩⟩

def Program lab ReturnType := Σ n, Program.Sized lab ReturnType n

def Program.Sized.result {lab : Ecosystem.Label} {ReturnType} {n : Nat} (prog : Program.Sized lab ReturnType n)
  : Σ (params : Program.Parameters), params.Product → ReturnType :=
  match prog with
  | .constructor (n := a) _ _ _ next =>
    let helper (prog : Program.Sized lab ReturnType a)
            : Σ (params : Program.Parameters), params.Product → ReturnType := prog.result
    ⟨.genId (fun objId => helper (next objId) |>.fst),
      fun ⟨objId, vals⟩ => helper (next objId) |>.snd vals⟩
  | .destructor _ _ _ _ next => next.result
  | .method _ _ _ _ next => next.result
  | .fetch (n := a) objId next =>
    let helper (prog : Program.Sized lab ReturnType a)
            : Σ (params : Program.Parameters), params.Product → ReturnType := prog.result
    ⟨.fetch objId (fun obj => helper (next obj) |>.fst),
      fun ⟨obj, vals⟩ => helper (next obj) |>.snd vals⟩
  | .invoke (n := a) p next =>
    let helper {ReturnType} (prog : Program.Sized lab ReturnType a)
            : Σ (params : Program.Parameters), params.Product → ReturnType := prog.result
    let ⟨pParams, pReturn⟩ := helper p
    let params :=
      pParams.append (fun pVals =>
        helper (next (pReturn pVals)) |>.fst)
    ⟨params, fun vals =>
      let ⟨pVals, vals'⟩ := Program.Parameters.splitProduct vals
      result (next (pReturn pVals)) |>.snd vals'⟩
  | .return val => ⟨.empty, fun () => val⟩

def Program.result {lab : Ecosystem.Label} {ReturnType} (prog : Program lab ReturnType)
  : Σ (params : Program.Parameters), params.Product → ReturnType :=
  prog.snd.result

/-- All body parameters - the parameters at the point of the return statement. -/
def Program.params {lab ReturnType} (prog : Program lab ReturnType) : Program.Parameters :=
  prog.result.fst

def Program.returnValue {lab ReturnType} (prog : Program lab ReturnType) (vals : prog.params.Product) : ReturnType :=
  prog.result.snd vals
