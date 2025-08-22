import Anoma
import AVM.Object
import AVM.Message
import AVM.Action
import AVM.Task.Parameters

namespace AVM

structure Task.Actions where
  actions : List Anoma.Action
  deltaWitness : Anoma.DeltaWitness

structure Task where
  /-- Task parameters - objects to fetch from the Anoma system and new object
    ids to generate. -/
  params : Task.Parameters
  /-- The message to send to the recipient. -/
  message : params.Product → SomeMessage
  /-- Task actions - actions to perform parameterised by fetched objects. -/
  actions : params.Product → Rand (Option Task.Actions)
deriving Inhabited

structure Task' (eparams : Task.Parameters) where
  /-- Task parameters - objects to fetch from the Anoma system and new object
    ids to generate. -/
  params : Task.Parameters
  /-- The message to send to the recipient. -/
  message : eparams.Product → params.Product → SomeMessage
  /-- Task actions - actions to perform parameterised by fetched objects. -/
  actions : eparams.Product → params.Product → Rand (Option Task.Actions)
deriving Inhabited

def Task'.toTask {eparams} (task : Task' eparams) : Task :=
  { params := eparams.append (fun _ => task.params),
    message := fun vals =>
      let ⟨vals1, vals2⟩ := Task.Parameters.splitProduct vals
      task.message vals1 vals2,
    actions := fun vals =>
      let ⟨vals1, vals2⟩ := Task.Parameters.splitProduct vals
      task.actions vals1 vals2 }

inductive Tasks.{u} : Task.Parameters.{u} → Type (u + 1) where
  | empty {params} : Tasks params
  | cons {params} (task : Task' params) (rest : Tasks params) : Tasks params
  | fetch {params} (objId : params.Product → TypedObjectId) (rest : Tasks (params.snocFetch objId)) : Tasks params
  | genId {params} (rest : Tasks params.snocGenId) : Tasks params

def Tasks.Products.{u} {ps} (tasks : Tasks.{u} ps) : List (Type u) :=
  match tasks with
  | .empty => []
  | .cons task rest => (ps.append (fun _ => task.params) |>.Product) :: rest.Products
  | .fetch _ rest => rest.Products
  | .genId rest => rest.Products

def Tasks.makeActions {ps}
  (tasks : Tasks ps)
  (vals : HList tasks.Products)
  : Rand (Option Task.Actions) :=
  match tasks, vals with
  | .empty, _ => pure <| some { actions := [], deltaWitness := Anoma.DeltaWitness.empty }
  | .cons task rest, HList.cons vals' vals'' => do
    let ⟨vals1, vals2⟩ := Task.Parameters.splitProduct vals'
    let try actions ← task.actions vals1 vals2
    let try rest ← makeActions rest vals''
    pure <| some <|
      { actions := actions.actions ++ rest.actions,
        deltaWitness := Anoma.DeltaWitness.compose actions.deltaWitness rest.deltaWitness }
  | .fetch _ rest, vals' => makeActions rest vals'
  | .genId rest, vals' => makeActions rest vals'

def Tasks.composeMessages {ps} (tasks : Tasks ps) (vals : HList tasks.Products) : List SomeMessage :=
  match tasks, vals with
  | .empty, _ => []
  | .cons task tasks', HList.cons vals' vals'' =>
    let ⟨vals1, vals2⟩ := Task.Parameters.splitProduct vals'
    task.message vals1 vals2 :: composeMessages tasks' vals''
  | .fetch _ tasks', vals' => composeMessages tasks' vals'
  | .genId tasks', vals' => composeMessages tasks' vals'

def Tasks.composeParams {ps} (tasks : Tasks ps) (vals : ps.Product) : Task.Parameters :=
  match tasks with
  | .empty => .empty
  | .cons task rest => task.params.append (fun _ => composeParams rest vals)
  | .fetch objId rest =>
    .fetch (objId vals) (fun obj =>
      let vals' := Task.Parameters.Values.snocFetch objId vals obj
      composeParams rest vals')
  | .genId rest => .genId (fun id =>
      let vals' := Task.Parameters.Values.snocGenId vals id
      composeParams rest vals')

def Tasks.composeParams' (tasks : Tasks .empty) : Task.Parameters :=
  @composeParams .empty tasks .unit

def Tasks.decomposeProduct {ps} (tasks : Tasks ps) (vals' : ps.Product) (vals : tasks.composeParams vals' |>.Product) : HList tasks.Products :=
  match tasks with
  | .empty => .nil
  | .cons _ rest =>
    let ⟨vals1, vals2⟩ := Task.Parameters.splitProduct vals
    let rest' := decomposeProduct rest vals' vals2
    HList.cons (Task.Parameters.Values.join vals' vals1) rest'
  | .fetch objId rest =>
    let ⟨obj, vals1⟩ := vals
    decomposeProduct rest (Task.Parameters.Values.snocFetch objId vals' obj) vals1
  | .genId rest =>
    let ⟨objId, vals1⟩ := vals
    decomposeProduct rest (Task.Parameters.Values.snocGenId vals' objId) vals1

def Tasks.composeActions {α}
  (tasks : α → Tasks .empty)
  (mkAction : (a : α) → HList (tasks a).Products → Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
  : (Σ a : α, (tasks a).composeParams'.Product) → Rand (Option Task.Actions) :=
  fun ⟨a, vals⟩ => do
    let vals' := Tasks.decomposeProduct (tasks a) .unit vals
    let try actions ← Tasks.makeActions (tasks a) vals'
    let try (action, witness) ← mkAction a vals'
    pure <| some <|
      { actions := action :: actions.actions,
        deltaWitness := Anoma.DeltaWitness.compose witness actions.deltaWitness }

def Tasks.composeWithFetchAction
  (msg : SomeMessage)
  (objId : TypedObjectId)
  (tasks : Object objId.classLabel → Tasks .empty)
  (mkAction : (obj : Object objId.classLabel) → HList (tasks obj).Products → Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
  : Task :=
  { params := .fetch objId (composeParams' ∘ tasks),
    message := fun _ => msg,
    actions := composeActions tasks mkAction }

def Tasks.composeWithFetch
  (msg : SomeMessage)
  (consumedObjectId : TypedObjectId)
  (tasks : Object consumedObjectId.classLabel → Tasks .empty)
  (createdObjects : Object consumedObjectId.classLabel → List CreatedObject)
  : Task :=
  let mkAction (obj : Object consumedObjectId.classLabel) (vals : HList (tasks obj).Products)
    : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
    let try consumedObject := obj.toConsumedObject false
    let createdMessages := composeMessages (tasks obj) vals
    Action.create [consumedObject] (createdObjects obj) [msg] createdMessages
  Tasks.composeWithFetchAction msg consumedObjectId tasks mkAction

def Tasks.composeWithGenIdAction
  (message : ObjectId → SomeMessage)
  (tasks : ObjectId → Tasks .empty)
  (mkAction : (objId : ObjectId) → HList (tasks objId).Products → Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
  : Task :=
  { params := .genId (composeParams' ∘ tasks),
    message := fun ⟨objId, _⟩ => message objId,
    actions := composeActions tasks mkAction }

def Tasks.composeWithGenId
  (message : ObjectId → SomeMessage)
  (tasks : ObjectId → Tasks .empty)
  (mkConsumedObject : ObjectId → SomeObject)
  (createdObjects : ObjectId → List CreatedObject)
  : Task :=
  let mkAction (objId : ObjectId) (vals : HList (tasks objId).Products)
    : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
    let try consumedObject := mkConsumedObject objId |>.toConsumedObject true
    let createdMessages := composeMessages (tasks objId) vals
    Action.create [consumedObject] (createdObjects objId) [message objId] createdMessages
  Tasks.composeWithGenIdAction message tasks mkAction
