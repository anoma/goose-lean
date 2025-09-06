import AVM.Task

namespace AVM

inductive Tasks (α : Type u) where
  | task (task : Task) (rest : task.params.Product → Tasks α) : Tasks α
  | fetch (param : TypedObjectId) (rest : Object param.classLabel → Tasks α) : Tasks α
  | result (value : α) : Tasks α

def Tasks.params {α} (tasks : Tasks α) : Program.Parameters :=
  match tasks with
  | .task t rest => (t.params.append (fun vals => (rest vals).params))
  | .fetch p rest => .fetch p (fun obj => (rest obj).params)
  | .result _ => .empty

def Tasks.map {α β} (tasks : Tasks α) (f : tasks.params.Product → α → β) : Tasks β :=
  match tasks with
  | .task t rest => .task t (fun vals => map (rest vals) (fun vals' => f (vals.append vals')))
  | .fetch p rest => .fetch p (fun obj => map (rest obj) (fun vals' => f ⟨obj, vals'⟩))
  | .result v => .result (f () v)

def Tasks.coerce {α β} {tasks : Tasks α} {f : tasks.params.Product → α → β} (vals : (tasks.map f).params.Product) : tasks.params.Product :=
  match tasks with
  | .task _ _ =>
    let ⟨vals1, vals2⟩ := vals.split
    vals1.append (coerce vals2)
  | .fetch _ _ =>
    let ⟨obj, vals'⟩ := vals
    ⟨obj, coerce vals'⟩
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
  (msg : tasks.params.Product → SomeMessage)
  (objects : tasks.params.Product → α → List SomeConsumableObject × List CreatedObject)
  : Task :=
  let mkAction (vals : tasks.params.Product) (a : α)
    : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
    let (consumedObjs, createdObjects) := objects vals a
    let try consumedObjects := consumedObjs.map (·.consume) |>.getSome
    let createdMessages := composeMessages tasks vals
    Action.create consumedObjects createdObjects [msg vals] createdMessages
  Tasks.composeWithAction (tasks.map mkAction) (fun vals => some (msg (coerce vals)))

def Tasks.compose (tasks : Tasks Unit) : Task :=
  let mkAction (vals : tasks.params.Product) (_ : Unit)
    : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
    let createdMessages := tasks.composeMessages vals
    Action.create [] [] [] createdMessages
  Tasks.composeWithAction (tasks.map mkAction) (fun _ => none)
