import Mathlib.Control.Random
import Anoma
import AVM.Tasks
import AVM.Ecosystem
import AVM.Class.Translation.Messages

namespace AVM.Class

abbrev AdjustFun := {clab : Class.Label} → Object clab → Object clab

structure Task' where
  task : Task
  adjust : task.params.Product → AdjustFun
  deriving Inhabited

structure TasksResult (params : Program.Parameters) (α : Type u) where
  adjust : AdjustFun
  value : α
  /-- Body parameter values adjusted by modifications in the program. -/
  bodyParameterValues : params.Product
  deriving Inhabited

mutual

partial def Body.tasks'
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
        Body.tasks' (task.adjust vals ∘ adjust) eco (next newId)
        |>.map (fun v => ⟨v.adjust, v.value, ⟨newId, v.bodyParameterValues⟩⟩)
  | .destructor classId destrId selfId args next =>
    let destr := eco.classes classId |>.destructors destrId
    Tasks.fetch ⟨classId.label, selfId⟩ fun self => Tasks.rand fun r =>
      let task := destr.task' adjust eco r self args
      Tasks.task task.task fun vals =>
        Body.tasks' (task.adjust vals ∘ adjust) eco next
  | .method classId methodId selfId args next =>
    let method := eco.classes classId |>.methods methodId
    Tasks.fetch ⟨classId.label, selfId⟩ fun self => Tasks.rand fun r =>
      let task := method.task' adjust eco r self args
      Tasks.task task.task fun vals =>
        Body.tasks' (task.adjust vals ∘ adjust) eco next
  | .fetch objId next =>
    Tasks.fetch objId fun obj =>
      Body.tasks' adjust eco (next (adjust obj))
      |>.map (fun v => ⟨v.adjust, v.value, ⟨adjust obj, v.bodyParameterValues⟩⟩)
  | .return val =>
    Tasks.result { adjust := adjust, value := val, bodyParameterValues := () }

partial def Member.task'
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
partial def Constructor.task'
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
  let mkActionData (newObjectData : ObjectData classId.label)
      : List SomeConsumableObject × List CreatedObject :=
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
partial def Destructor.task'
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
  let mkActionData (_ : Unit)
      : List SomeConsumableObject × List CreatedObject :=
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

partial def Method.task'
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
  let mkActionData (obj : Object classId.label)
      : List SomeConsumableObject × List CreatedObject :=
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

def Body.tasks
  {α}
  [Inhabited α]
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (prog : Program lab α)
  : Tasks α :=
  Body.tasks' id eco prog |>.map TasksResult.value
