import AVM.Object
import AVM.Class.Label
import AVM.Ecosystem.Label
import AVM.Program.Parameters
import AVM.Scope.Label

namespace AVM

/-- Representation of AVM programs. These are compiled to Anoma programs. -/
inductive Program.{u} (scope : Scope.Label) (ReturnType : Type u) : Type (max u 1) where
  | /-- Constructor call. -/
    constructor
    (eid : scope.EcosystemId)
    (cid : eid.label.ClassId)
    (constrId : cid.label.ConstructorId)
    (args : constrId.Args.type)
    (signatures : constrId.Signatures args)
    (next : ObjectId → Program scope ReturnType)
    : Program scope ReturnType
  | /-- Destructor call. -/
    destructor
    (eid : scope.EcosystemId)
    (cid : eid.label.ClassId)
    (destrId : cid.label.DestructorId)
    (selfId : ObjectId)
    (args : destrId.Args.type)
    (signatures : destrId.Signatures args)
    (next : Program scope ReturnType)
    : Program scope ReturnType
  | /-- Method call. -/
    method
    (eid : scope.EcosystemId)
    (cid : eid.label.ClassId)
    (methodId : cid.label.MethodId)
    (selfId : ObjectId)
    (args : methodId.Args.type)
    (signatures : methodId.Signatures args)
    (next : Program scope ReturnType)
    : Program scope ReturnType
  | /-- MultiMethod call. -/
    multiMethod
    (eid : scope.EcosystemId)
    (mid : eid.label.MultiMethodId)
    (selvesIds : mid.SelvesIds)
    (args : mid.Args.type)
    (signatures : mid.Signatures args)
    (next : Program scope ReturnType)
    : Program scope ReturnType
  | /-- Object upgrade -/
    upgrade
    (eid : scope.EcosystemId)
    (cid : eid.label.ClassId)
    (selfId : ObjectId)
    (objData : SomeObjectData)
    (next : Program scope ReturnType)
    : Program scope ReturnType
  | /-- Object fetch by object id. -/
    fetch
    {ecoLab : Ecosystem.Label}
    {classId : ecoLab.ClassId}
    (objId : ObjectId)
    (next : Object classId → Program scope ReturnType)
    : Program scope ReturnType
  | /-- Return value. -/
    return
    (val : ReturnType)
    : Program scope ReturnType

namespace Program

def lift.{v, u}
  {lab}
  {α : Type u}
  (prog : Program lab α)
  : Program.{max u v} lab (ULift α) :=
  match prog with
  | .constructor eid cid constr args signatures next => .constructor eid cid constr args signatures (fun a => (next a).lift)
  | .destructor eid cid destrId selfId args signatures next => .destructor eid cid destrId selfId args signatures next.lift
  | .method eid cid methodId selfId args signatures next => .method eid cid methodId selfId args signatures next.lift
  | .multiMethod eid mid selvesIds args signatures next => .multiMethod eid mid selvesIds args signatures next.lift
  | .upgrade eid cid selfId obj next => .upgrade eid cid selfId obj next.lift
  | .fetch objId next => .fetch objId (fun a => (next a).lift)
  | .return val => .return (ULift.up val)

/-- Program composition: invoke a program and then continue with another program. -/
def invoke
    {α β : Type u}
    {lab : Scope.Label}
    (prog : Program lab α)
    (next : α → Program lab β)
    : Program lab β :=
  match prog with
  | .constructor eid cid constrId args signatures cont =>
    .constructor eid cid constrId args signatures (fun objId => Program.invoke (cont objId) next)
  | .destructor eid cid destrId selfId args signatures cont =>
    .destructor eid cid destrId selfId args signatures (Program.invoke cont next)
  | .method eid cid methodId selfId args signatures cont =>
    .method eid cid methodId selfId args signatures (Program.invoke cont next)
  | .multiMethod eid mid selvesId args signatures cont =>
    .multiMethod eid mid selvesId args signatures (Program.invoke cont next)
  | .upgrade eid cid selfId obj cont =>
    .upgrade eid cid selfId obj (Program.invoke cont next)
  | .fetch objId cont =>
    .fetch objId (fun obj => Program.invoke (cont obj) next)
  | .return val =>
    next val

/-- Parameters (generated random values and fetched obejcts) of the program,
  *not* including the parameters of the sub-programs (the bodies of called
  methods, constructors, destructors). In general, values of type
  `prog.params.Product` are assumed to be adjusted (see
  `Program.Parameters.Product`). -/
def params {lab : Scope.Label} {α : Type u} (prog : Program lab α) : Parameters :=
  match prog with
  | .constructor _ _ _ _ _ next => .genId (fun newId => next newId |>.params)
  | .destructor _ _ _ _ _ _ next => next.params
  | .method _ _ _ _ _ _ next => next.params
  | .multiMethod _ _ _ _ _ next => next.params
  | .upgrade _ _ _ _ next => next.params
  | .fetch objId next => .fetch objId (fun obj => next obj |>.params)
  | .return _ => .empty

/-- The return value of a program. The `vals` provided need to be adjusted (see
  `Program.Parameters.Product`). -/
def value {lab : Scope.Label} {α : Type u} (prog : Program lab α) (vals : prog.params.Product) : α :=
  match prog with
  | .constructor _ _ _ _ _ next =>
    let ⟨newId, vals'⟩ := vals
    next newId |>.value vals'
  | .destructor _ _ _ _ _ _ next =>
    next.value vals
  | .method _ _ _ _ _ _ next =>
    next.value vals
  | .multiMethod _ _ _ _ _ next =>
    next.value vals
  | .upgrade _ _ _ _ next =>
    next.value vals
  | .fetch _ next =>
    let ⟨obj, vals'⟩ := vals
    next obj |>.value vals'
  | .return val =>
    val
