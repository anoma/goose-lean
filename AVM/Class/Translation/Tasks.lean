import Mathlib.Control.Random
import Anoma
import AVM.Tasks
import AVM.Ecosystem
import AVM.Class.Translation.Messages

namespace AVM.Class

/-- Type of functions which adjust object values by modifications that occurred
  in the program up to a certain point. -/
abbrev AdjustFun := {clab : Class.Label} → Object clab → Object clab

private structure Task' where
  task : Task
  /-- Function which adjusts object values by modifications that occurred in the
    program up to the point after the task, i.e., up to and including the part
    of the program corresponding to the task. -/
  adjust : task.params.Product → AdjustFun
  deriving Inhabited

/-- A helper type for data at the end of `Tasks` execution. -/
private structure TasksResult (params : Program.Parameters) (α : Type u) where
  /-- The return value of the tasks. -/
  value : α
  /-- Function which adjusts object values by modifications that occurred in the
    program up to after the tasks, i.e., up to and including the part of the
    program corresponding to the tasks. -/
  adjust : AdjustFun
  /-- Body parameter values adjusted by preceding modifications in the program. -/
  bodyParameterValues : params.Product
  deriving Inhabited

mutual

/-- Creates `Tasks` for a given `body` program. The `adjust` argument adjusts
   object values by modifications that occurred in the program up to before
   executing `body`. The result in `TasksResult` contains:
 1. The return value of the body.
 2. The `adjust` function which adjusts object values by modifications that
    occurred in the program up to after executing `body`.
 3. The adjusted values of body parameters (adjusted values in
    `body.params.Product`). -/
private partial def Body.tasks'
  (adjust : AdjustFun)
  {α}
  [Inhabited α]
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (body : Program lab α)
  : Tasks (TasksResult body.params α) :=
  match body with
  | .constructor classId constrId args next =>
    let constr := eco.classes classId |>.constructors constrId
    Tasks.rand fun newId => Tasks.rand fun r =>
      let task := constr.task' adjust eco newId r args
      Tasks.task task.task fun vals =>
        Body.tasks' (task.adjust vals) eco (next newId)
        |>.map (fun res => ⟨res.value, res.adjust, ⟨newId, res.bodyParameterValues⟩⟩)
  | .destructor classId destrId selfId args next =>
    let destr := eco.classes classId |>.destructors destrId
    Tasks.fetch selfId fun self => Tasks.rand fun r =>
      let task := destr.task' adjust eco r (adjust self) args
      Tasks.task task.task fun vals =>
        Body.tasks' (task.adjust vals) eco next
  | .method classId methodId selfId args next =>
    let method := eco.classes classId |>.methods methodId
    Tasks.fetch selfId fun self => Tasks.rand fun r =>
      let task := method.task' adjust eco r (adjust self) args
      Tasks.task task.task fun vals =>
        Body.tasks' (task.adjust vals) eco next
  | .fetch objId next =>
    Tasks.fetch objId fun obj =>
      Body.tasks' adjust eco (next (adjust obj))
      |>.map (fun res => ⟨res.value, res.adjust, ⟨adjust obj, res.bodyParameterValues⟩⟩)
  | .return val =>
    Tasks.result ⟨val, adjust, ()⟩

private partial def Member.task'
  {α}
  [Inhabited α]
  (adjust : AdjustFun)
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (body : Program lab α)
  (mkActionData : α → List SomeConsumableObject × List CreatedObject)
  (mkMessage : body.params.Product → SomeMessage)
  : Task' :=
  let tasks : Tasks (TasksResult body.params α) :=
    Body.tasks' adjust eco body
  let task :=
    Tasks.composeWithMessage
      tasks
      (fun res => mkMessage res.bodyParameterValues)
      (mkActionData ∘ TasksResult.value)
  let mkAdjust (vals : task.params.Product) : AdjustFun :=
    let res := tasks.value (Tasks.coerce vals)
    let (_, createdObjects) := mkActionData res.value
    let adjust' : AdjustFun := fun obj =>
      let try createdObj := createdObjects.find? (fun o => o.uid == obj.uid)
          failwith obj
      let try obj' := tryCast createdObj.toObject
          failwith obj
      obj'
    adjust' ∘ res.adjust
  ⟨task, mkAdjust⟩

/-- Creates a Task for a given object constructor. -/
private partial def Constructor.task'
  (adjust : AdjustFun)
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  (newId : ObjectId)
  (r : Nat)
  (args : constrId.Args.type)
  : Task' :=
  let body : Program lab (ObjectData classId.label) := constr.body args
  let mkActionData (newObjectData : ObjectData classId.label) : List SomeConsumableObject × List CreatedObject :=
    let newObj : SomeObject :=
      let obj : Object classId.label :=
        { uid := newId,
          nonce := ⟨newId⟩,
          data := newObjectData }
      obj.toSomeObject
    let consumedObj := newObj.toConsumable (ephemeral := true)
    let createdObjects : List CreatedObject :=
      [CreatedObject.fromSomeObject newObj (ephemeral := false) (rand := r)]
    ([consumedObj], createdObjects)
  let mkMessage (vals : body.params.Product) : SomeMessage :=
    constr.message ⟨body.params.Product⟩ vals newId args
  Member.task' adjust eco body mkActionData mkMessage

/-- Creates a Task for a given object destructor. -/
private partial def Destructor.task'
  (adjust : AdjustFun)
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor classId destructorId)
  (r : Nat)
  (self : Object classId.label)
  (args : destructorId.Args.type)
  : Task' :=
  let body : Program lab Unit := destructor.body self args
  let mkActionData (_ : Unit) : List SomeConsumableObject × List CreatedObject :=
    let consumedObj := self.toSomeObject.toConsumable (ephemeral := false)
    let createdObjects : List CreatedObject :=
      [{ uid := self.uid,
         data := self.data,
         ephemeral := true,
         rand := r }]
    ([consumedObj], createdObjects)
  let mkMessage (vals : body.params.Product) : SomeMessage :=
    destructor.message ⟨body.params.Product⟩ vals self.uid args
  Member.task' adjust eco body mkActionData mkMessage

/-- Creates a Task for a given method. -/
private partial def Method.task'
  (adjust : AdjustFun)
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (r : Nat)
  (self : Object classId.label)
  (args : methodId.Args.type)
  : Task' :=
  let body : Program lab (Object classId.label) := method.body self args
  let mkActionData (obj : Object classId.label) : List SomeConsumableObject × List CreatedObject :=
    let consumedObj := self.toSomeObject.toConsumable (ephemeral := false)
    let createdObjects : List CreatedObject :=
      [{ uid := obj.uid,
         data := obj.data,
         ephemeral := false,
         rand := r }]
    ([consumedObj], createdObjects)
  let mkMessage (vals : body.params.Product) : SomeMessage :=
    method.message ⟨body.params.Product⟩ vals self.uid args
  Member.task' adjust eco body mkActionData mkMessage

end -- mutual

/-- Creates Tasks for a given class member body program. -/
def Member.Body.tasks
  {α}
  [Inhabited α]
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (prog : Program lab α)
  : Tasks α :=
  Body.tasks' id eco prog |>.map TasksResult.value
