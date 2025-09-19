import Mathlib.Control.Random
import Anoma
import AVM.Tasks
import AVM.Ecosystem
import AVM.Class.Translation.Messages
import AVM.Action

namespace AVM

/-- Type of functions which adjust object values by modifications that occurred
  in the program up to a certain point. -/
abbrev AdjustFun := {lab : Ecosystem.Label} → {c : lab.ClassId} → Object c → Object c

private structure Task' where
  task : Task
  /-- Function which adjusts object values by modifications that occurred in the
    program up to the point after the task, i.e., up to and including the part
    of the program corresponding to the task. -/
  adjust : task.params.Product → AdjustFun
  deriving Inhabited

/-- A helper type for data at the end of `Tasks` execution. -/
private structure TasksResult (params : Program.Parameters) (α : Type u) : Type (max 2 u) where
  /-- The return value of the tasks. -/
  value : α
  /-- Function which adjusts object values by modifications that occurred in the
    program up to after the tasks, i.e., up to and including the part of the
    program corresponding to the tasks. -/
  adjust : AdjustFun
  /-- Body parameter values adjusted by preceding modifications in the program. -/
  bodyParameterValues : params.Product
  deriving Inhabited

private structure MultiTasksResult {lab : Ecosystem.Label} (multiId : lab.MultiMethodId) where
  res : MultiMethodResult multiId
  rands : MultiMethodRandoms res.data
  deriving Inhabited

private def mkReturn {α} (val : α) (adjust : AdjustFun) : Tasks (TasksResult .empty α) :=
  .result ⟨val, adjust, ⟨⟩⟩

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
  {α β : Type 1}
  [Inhabited β]
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (body : Program lab α)
  (cont : α → AdjustFun → Tasks (TasksResult .empty β))
  : Tasks (TasksResult body.params β) :=
  match body with
  | .constructor classId constrId args next =>
    let constr := eco.classes classId |>.constructors constrId
    Tasks.rand fun newId => Tasks.rand fun r =>
      let task := constr.task' adjust eco newId r args
      Tasks.task task.task fun vals =>
        Body.tasks' (task.adjust vals) eco (next newId) cont
        |>.map (fun res => ⟨res.value, res.adjust, ⟨newId, res.bodyParameterValues⟩⟩)
  | .destructor classId destrId selfId args next =>
    let destr := eco.classes classId |>.destructors destrId
    Tasks.fetch selfId fun self => Tasks.rand fun r =>
      let task := destr.task' adjust eco r (adjust self) args
      Tasks.task task.task fun vals =>
        Body.tasks' (task.adjust vals) eco next cont
  | .method classId methodId selfId args next =>
    let method := eco.classes classId |>.methods methodId
    Tasks.fetch selfId fun self => Tasks.rand fun r =>
      let task := method.task' adjust eco r (adjust self) args
      Tasks.task task.task fun vals =>
        Body.tasks' (task.adjust vals) eco next cont
  | .multiMethod multiId selvesIds args next =>
    Tasks.fetchSelves selvesIds fun selves =>
      let task := multiId.task' adjust eco (fun x => adjust (selves x)) args
      Tasks.task task.task fun vals =>
        Body.tasks' (task.adjust vals) eco next cont
  | .upgrade classId selfId obj next =>
    Tasks.fetch selfId fun self => Tasks.rand fun r =>
      let obj' := {obj with object := adjust obj.object}
      let task := Class.Upgrade.task' (classId := classId) adjust eco r (adjust self) obj'
      Tasks.task task.task fun vals =>
        Body.tasks' (task.adjust vals) eco next cont
  | .fetch objId next =>
    Tasks.fetch objId fun obj =>
      Body.tasks' adjust eco (next (adjust obj)) cont
      |>.map (fun res => ⟨res.value, res.adjust, ⟨adjust obj, res.bodyParameterValues⟩⟩)
  | .return val =>
    cont val adjust

private partial def Body.task'
  {α β : Type 1}
  [i : Inhabited β]
  (adjust : AdjustFun)
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (body : Program lab α)
  (cont : α → AdjustFun → Tasks (TasksResult .empty β))
  (mkActionData : β → ActionData)
  (mkMessage : body.params.Product → SomeMessage)
  : Task' :=
  let tasks : Tasks (TasksResult body.params β) :=
    Body.tasks' adjust eco body cont
  let task :=
    Tasks.composeWithMessage
      tasks
      (fun res => mkMessage res.bodyParameterValues)
      (fun res => mkActionData res.value)
  let mkAdjust (vals : task.params.Product) : AdjustFun :=
    let res := tasks.value (Tasks.coerce vals)
    let actionData := mkActionData res.value
    let adjust' : AdjustFun := fun obj =>
      -- NOTE: This doesn't take into account objects that are destroyed. If an
      -- object is fetched after being destroyed, the program behaviour is
      -- undefined.
      let try createdObj := actionData.created.find? (fun o => o.uid == obj.uid)
          failwith obj
      let try obj' := tryCast createdObj.toObject
          failwith obj
      obj'
    adjust' ∘ res.adjust
  ⟨task, mkAdjust⟩

/-- Creates a Task for a given object constructor. -/
private partial def Class.Constructor.task'
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
  let body : Program.{1} lab (ULift (ObjectData classId)) := constr.body args |>.lift
  let mkActionData (newObjectData : ULift (ObjectData classId)) : ActionData :=
    let newObj : SomeObject :=
      let obj : Object classId :=
        { uid := newId,
          nonce := ⟨newId⟩,
          data := newObjectData.down }
      obj.toSomeObject
    let consumedObj := newObj.toConsumable (ephemeral := true)
    let createdObjects : List CreatedObject :=
      [CreatedObject.fromSomeObject newObj (ephemeral := false) (rand := r)]
    { consumed := [consumedObj]
      created := createdObjects }
  let mkMessage (vals : body.params.Product) : SomeMessage :=
    constr.message ⟨body.params.Product⟩ vals newId args
  Body.task' adjust eco body mkReturn mkActionData mkMessage

/-- Creates a Task for a given object destructor. -/
private partial def Class.Destructor.task'
  (adjust : AdjustFun)
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor classId destructorId)
  (r : Nat)
  (self : Object classId)
  (args : destructorId.Args.type)
  : Task' :=
  let body : Program.{1} lab (ULift Unit) := destructor.body self args |>.lift
  let mkActionData (_ : ULift Unit) : ActionData :=
    let consumedObj := self.toSomeObject.toConsumable (ephemeral := false)
    let createdObjects : List CreatedObject :=
      [{ uid := self.uid,
         data := self.data,
         ephemeral := true,
         rand := r }]
    { consumed := [consumedObj]
      created := createdObjects }
  let mkMessage (vals : body.params.Product) : SomeMessage :=
    destructor.message ⟨body.params.Product⟩ vals self.uid args
  Body.task' adjust eco body mkReturn mkActionData mkMessage

/-- Creates a Task for a given method. -/
private partial def Class.Method.task'
  (adjust : AdjustFun)
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (r : Nat)
  (self : Object classId)
  (args : methodId.Args.type)
  : Task' :=
  let body : Program.{1} lab (ULift (Object classId)) := method.body self args |>.lift
  let mkActionData (lobj : ULift (Object classId)) : ActionData :=
    let consumedObj := self.toSomeObject.toConsumable (ephemeral := false)
    let obj : Object classId := lobj.down
    let createdObject : CreatedObject :=
      { uid := obj.uid,
         data := obj.data,
         ephemeral := false,
         rand := r }
    { consumed := [consumedObj]
      created := [createdObject] }
  let mkMessage (vals : body.params.Product) : SomeMessage :=
    method.message ⟨body.params.Product⟩ vals self.uid args
  Body.task' adjust eco body mkReturn mkActionData mkMessage

private partial def Class.Upgrade.task'
  (adjust : AdjustFun)
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  (r : Nat)
  (self : Object classId)
  (obj : SomeObject)
  : Task' :=
  let mkActionData (_ : PUnit) : ActionData :=
    let consumedObj := self.toSomeObject.toConsumable (ephemeral := false)
    let createdObject : CreatedObject :=
      { uid := obj.object.uid,
         data := obj.object.data,
         ephemeral := false,
         rand := r }
    { consumed := [consumedObj]
      created := [createdObject] }
  let mkMessage (_ : PUnit) : SomeMessage :=
    Class.Upgrade.message classId self.uid
  Body.task' adjust eco (.return PUnit.unit) mkReturn mkActionData mkMessage

partial def Ecosystem.Label.MultiMethodId.task'
  (adjust : AdjustFun)
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {multiId : lab.MultiMethodId}
  (selves : multiId.Selves)
  (args : multiId.Args.type)
  : Task' :=
  let method := eco.multiMethods multiId
  let body := method.body selves args

  let mkResult (res : MultiMethodResult multiId) (adjust : AdjustFun) : Tasks (TasksResult .empty (MultiTasksResult multiId)) :=
    Tasks.genMultiMethodRandoms res.data fun rands =>
      mkReturn ⟨res, rands⟩ adjust

  let mkActionData
      (tasksRes : MultiTasksResult multiId)
      : ActionData :=
      let res := tasksRes.res
      let rands := tasksRes.rands
      let consumedSelves := Ecosystem.Label.MultiMethodId.SelvesToVector selves (fun x => x.toSomeObject.toConsumable (ephemeral := false)) |>.toList
      let destroyed := res.destroyed
      let destroyedEph := destroyed.zipWith rands.destroyedEphRands.toList (f := fun c r => c.balanceDestroyed (rand := r))
      let reassembled := res.assembled.withNewUid.zipWith3 rands.reassembledNewUidRands.toList rands.reassembledNewUidNonces.toList (f := fun (obj : SomeObjectData) r nonce =>
            { label := obj.label
              classId := obj.classId
              data := obj.data
              ephemeral := false
              uid := nonce.value
              rand := r
              : CreatedObject })
              ++ res.assembled.withOldUidList.zipWith rands.reassembledNewUidRands.toList (f := fun obj r =>
            { label := lab
              classId := obj.arg.classId
              data := obj.objectData
              ephemeral := false
              uid := selves obj.arg |>.uid
              rand := r
              : CreatedObject })
      let constructedSomeObjects := res.constructed.zipWith rands.constructedNonces.toList (f := fun c n =>
            { label := c.label
              classId := c.classId
              object :=
                { uid := n.value
                  nonce := n
                  data := c.data }
                  : SomeObject })
      let constructed := constructedSomeObjects.zipWith rands.constructedRands.toList (f := fun c r =>
            { label := c.label
              classId := c.classId
              uid := c.object.uid
              data := c.object.data
              ephemeral := false
              rand := r
              : CreatedObject })
      let constructedEph := constructedSomeObjects.map fun c => c.balanceConstructed
      let selvesDestroyedEph := multiId.objectArgNamesVec.toList.filterMap
          (fun a => match res.argDeconstruction a with
                    | .Destroyed =>
                      let consumable : SomeConsumableObject := ⟨(selves a).toConsumable (ephemeral := false)⟩
                      some (fun r => consumable.balanceDestroyed (rand := r))
                    | .Disassembled => none)
          |>.zipWith rands.selvesDestroyedEphRands.toList (f := fun mk r => mk r)
      { consumed := consumedSelves ++ constructedEph ++ destroyed
        created := reassembled ++ constructed ++ destroyedEph ++ selvesDestroyedEph
        ensureUnique := rands.reassembledNewUidNonces.toList }

  let mkMessage (vals : body.params.Product) : SomeMessage :=
    ⟨(eco.multiMethods multiId).message selves args body vals⟩

  Body.task' adjust eco body mkResult mkActionData mkMessage

end -- mutual

/-- Creates Tasks for a given class member body program. -/
def Member.Body.tasks
  {α : Type 1}
  [Inhabited α]
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (prog : Program lab α)
  : Tasks α :=
  Body.tasks' id eco prog mkReturn |>.map TasksResult.value
