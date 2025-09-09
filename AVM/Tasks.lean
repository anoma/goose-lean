import AVM.Task

namespace AVM

/-- The `Tasks` type represents a sequence of tasks with intervening object
  fetches and random value generations. The `Tasks` type mimics more closely the
  structure of AVM programs than a single `Task`. `AVM.Program` is compiled to
  `Tasks` which are then composed into a single `Task`. The composition of
  `Tasks` collects and lifts out the parameters of all subtasks. -/
inductive Tasks (α : Type u) where
  /-- Execute a subtask and continue. The `rest` continuation receives the
    unadjusted parameter values. -/
  | task (task : Task) (rest : task.params.Product → Tasks α) : Tasks α
  /-- Fetch an object and continue. The `rest` continuation receives the
    unadjusted original object value and is supposed to adjust it by the
    modifications to that object that occurred from the start of the program up
    to the fetch. -/
  | fetch {classLabel : Class.Label} (objId : ObjectId) (rest : Object classLabel → Tasks α) : Tasks α
  | rand (rest : Nat → Tasks α) : Tasks α
  | result (value : α) : Tasks α
  deriving Inhabited

/-- `Tasks.params` includes the parameters of the sub-tasks, in contrast to
  `Program.params` which doesn't include the parameters of the sub-programs. In
  general, values in `tasks.params.Product` are assumed to be unadjusted (see
  `Program.Parameters.Product`), in contrast to values in `prog.params.Product`
  which are assumed to be adjusted. -/
def Tasks.params {α} (tasks : Tasks α) : Program.Parameters :=
  match tasks with
  | .task t rest => (t.params.append (fun vals => (rest vals).params))
  | .fetch p rest => .fetch p (fun obj => (rest obj).params)
  | .rand rest => .rand (fun r => (rest r).params)
  | .result _ => .empty

/-- The return value of the tasks. `vals` are unadjusted parameter values (see
  `Program.Parameters.Product`): the object values as fetched from Anoma at the
  start of program execution, i.e., they are not adjusted by subsequent
  modifications to these objects in the program. -/
def Tasks.value {α} (tasks : Tasks α) (vals : tasks.params.Product) : α :=
  match tasks with
  | .task _ rest =>
    let ⟨vals1, vals2⟩ := vals.split
    Tasks.value (rest vals1) vals2
  | .fetch _ rest =>
    let ⟨obj, vals'⟩ := vals
    Tasks.value (rest obj) vals'
  | .rand rest =>
    let ⟨r, vals'⟩ := vals
    Tasks.value (rest r) vals'
  | .result v => v

def Tasks.map' {α β} (tasks : Tasks α) (f : tasks.params.Product → α → β) : Tasks β :=
  match tasks with
  | .task t rest => .task t (fun vals => map' (rest vals) (fun vals' => f (vals.append vals')))
  | .fetch p rest => .fetch p (fun obj => map' (rest obj) (fun vals' => f ⟨obj, vals'⟩))
  | .rand rest => .rand (fun r => map' (rest r) (fun vals' => f ⟨r, vals'⟩))
  | .result v => .result (f () v)

def Tasks.map {α β} (tasks : Tasks α) (f : α → β) : Tasks β :=
  tasks.map' (fun _ a => f a)

def Tasks.coerce {α β} {tasks : Tasks α} {f : tasks.params.Product → α → β} (vals : (tasks.map' f).params.Product) : tasks.params.Product :=
  match tasks with
  | .task _ _ =>
    let ⟨vals1, vals2⟩ := vals.split
    vals1.append (coerce vals2)
  | .fetch _ _ =>
    let ⟨obj, vals'⟩ := vals
    ⟨obj, coerce vals'⟩
  | .rand _ =>
    let ⟨r, vals'⟩ := vals
    ⟨r, coerce vals'⟩
  | .result _ => vals

def TasksWithAction := Tasks (Rand (Option (Anoma.Action × Anoma.DeltaWitness)))

def Tasks.composeActions
  (tasks : TasksWithAction)
  (vals : tasks.params.Product)
  : Rand (Option Task.Actions) :=
  match tasks with
  | .result v => do
    let try (action, witness) ← v
    pure <| some { actions := [action], deltaWitness := witness }
  | .task ta rest => do
    let ⟨vals1, vals2⟩ := vals.split
    let try actions ← ta.actions vals1
    let try rest' ← composeActions (rest vals1) vals2
    pure <| some <|
      { actions := actions.actions ++ rest'.actions,
        deltaWitness := Anoma.DeltaWitness.compose actions.deltaWitness rest'.deltaWitness }
  | .fetch _ rest =>
    let ⟨obj, vals'⟩ := vals
    composeActions (rest obj) vals'
  | .rand rest =>
    let ⟨r, vals'⟩ := vals
    composeActions (rest r) vals'

def Tasks.composeMessages {α} (tasks : Tasks α) (vals : tasks.params.Product) : List SomeMessage :=
  match tasks with
  | .result _ => []
  | .task ta tasks' =>
    let ⟨vals1, vals2⟩ := vals.split
    (ta.message vals1 |>.toList) ++
      composeMessages (tasks' vals1) vals2
  | .fetch _ rest =>
    let ⟨obj, vals'⟩ := vals
    composeMessages (rest obj) vals'
  | .rand rest =>
    let ⟨r, vals'⟩ := vals
    composeMessages (rest r) vals'

def Tasks.composeWithAction
  (tasks : TasksWithAction)
  (msg : tasks.params.Product → Option SomeMessage)
  : Task :=
  { params := tasks.params,
    message := msg,
    actions := composeActions tasks }

def Tasks.composeWithMessage
  {α}
  (tasks : Tasks α)
  (msg : α → SomeMessage)
  (objects : α → List SomeConsumableObject × List CreatedObject)
  : Task :=
  let mkAction (vals : tasks.params.Product) (a : α)
    : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
    let (consumedObjs, createdObjects) := objects a
    let try consumedObjects := consumedObjs.map (·.consume) |>.getSome
    let createdMessages := composeMessages tasks vals
    Action.create consumedObjects createdObjects [msg a] createdMessages
  Tasks.composeWithAction (tasks.map' mkAction) (fun vals => some (msg (tasks.value (coerce vals))))

def Tasks.compose (tasks : Tasks Unit) : Task :=
  let mkAction (vals : tasks.params.Product) (_ : Unit)
    : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
    let createdMessages := tasks.composeMessages vals
    Action.create [] [] [] createdMessages
  Tasks.composeWithAction (tasks.map' mkAction) (fun _ => none)
