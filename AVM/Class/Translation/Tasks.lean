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

mutual

partial def Program.tasks'
  (adjust : AdjustFun)
  {α}
  [Inhabited α]
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (prog : Program lab α)
  : Tasks (AdjustFun × α) :=
  match prog with
  | .constructor classId constrId args next =>
    let constr := eco.classes classId |>.constructors constrId
    Tasks.genId fun newId =>
      let task := constr.task' adjust eco newId args
      Tasks.task task.task fun vals =>
        Program.tasks' (task.adjust vals ∘ adjust) eco (next newId)
  | .destructor classId destrId selfId args next =>
    let destr := eco.classes classId |>.destructors destrId
    let task := destr.task' adjust eco selfId args
    Tasks.task task.task fun vals =>
      Program.tasks' (task.adjust vals ∘ adjust) eco next
  | .method classId methodId selfId args next =>
    let method := eco.classes classId |>.methods methodId
    let task := method.task' adjust eco selfId args
    Tasks.task task.task fun vals =>
      Program.tasks' (task.adjust vals ∘ adjust) eco next
  | .fetch objId next =>
    Tasks.fetch objId fun obj =>
      Program.tasks' adjust eco (next (adjust obj))
  | .return val =>
    Tasks.result (adjust, val)

/-- Creates a Task for a given object constructor. -/
partial def Constructor.task'
  (adjust : AdjustFun)
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  (newId : ObjectId)
  (args : constrId.Args.type)
  : Task' :=
  let mkActionData (adjust' : AdjustFun) (newObjData : ObjectData classId.label)
      : AdjustFun × List SomeConsumableObject × List CreatedObject :=
    let newObj : SomeObject :=
      let obj : Object classId.label :=
        { uid := newId,
          nonce := ⟨newId⟩,
          data := newObjData }
      obj.toSomeObject
    let consumedObj := newObj.toConsumable (ephemeral := true)
    let createdObjects : List CreatedObject :=
      [CreatedObject.fromSomeObject newObj (ephemeral := false)]
    (adjust', [consumedObj], createdObjects)
  let tasks := Program.tasks' adjust eco (constr.body args)
  let task :=
    Tasks.composeWithMessage
      tasks
      (fun vals => constr.message ⟨tasks.params.Product⟩ vals newId args)
      (fun _ => Prod.snd ∘ Function.uncurry mkActionData)
  let mkAdjust (vals : task.params.Product) : AdjustFun :=
    let (adjust', _, createdObjects) := Function.uncurry mkActionData (tasks.value (Tasks.coerce vals))
    let adjust'' : AdjustFun := fun obj =>
      let try createdObj := createdObjects.find? (fun o => o.uid == obj.uid)
          failwith obj
      obj
    adjust'' ∘ adjust' ∘ adjust
  ⟨task, mkAdjust⟩

/-- Creates a Task for a given object destructor. -/
partial def Destructor.task'
  (adjust : AdjustFun)
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor classId destructorId)
  (selfId : ObjectId)
  (args : destructorId.Args.type)
  : Task' :=
  let consumedObjectId : TypedObjectId := ⟨classId.label, selfId⟩
  let bodyParams (self : Object classId.label) := (destructor.body self args).params
  let params := Program.Parameters.fetch consumedObjectId bodyParams
  Task.absorbParams params fun ⟨self, vals⟩ =>
    let tasks : List Task := Program.tasks eco (destructor.body self args) vals
    let consumedObj := self.toSomeObject.toConsumable (ephemeral := false)
    let createdObjects : List CreatedObject :=
      [{ uid := self.uid,
         data := self.data,
         ephemeral := true }]
    Tasks.composeWithMessage (destructor.message ⟨(bodyParams self).Product⟩ vals selfId args) tasks [consumedObj] createdObjects

partial def Method.task'
  (adjust : AdjustFun)
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  : Task' :=
  let consumedObjectId : TypedObjectId := ⟨classId.label, selfId⟩
  let bodyParams (self : Object classId.label) := (method.body self args).params
  let params := Program.Parameters.fetch consumedObjectId bodyParams
  Task.absorbParams params fun ⟨self, vals⟩ =>
    let body := method.body self args
    let tasks : List Task := Program.tasks eco body vals
    let consumedObj := self.toSomeObject.toConsumable (ephemeral := false)
    let obj := (body.returnValue vals).toSomeObject
    let createdObjects : List CreatedObject :=
      [{ uid := obj.object.uid,
         data := obj.object.data,
         ephemeral := false }]
    Tasks.composeWithMessage (method.message ⟨(bodyParams self).Product⟩ vals selfId args) tasks [consumedObj] createdObjects

end -- mutual
