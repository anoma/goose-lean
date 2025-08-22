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

inductive Tasks.{u} : Task.Parameters.{u} → Type (u + 1) where
  | empty {params} : Tasks params
  | fetch {params} (objId : params.Product → TypedObjectId) (task : params.Product → Task) (rest : Tasks (params.snocFetch objId)) : Tasks params
  | genId {params} (task : params.Product → Task) (rest : Tasks params.snocGenId) : Tasks params

def Task.Products (tasks : List Task) : List Type :=
  tasks.map (·.params) |> .map (·.Product)

def Task.makeActions
  (tasks : List Task)
  (vals : HList (Products tasks))
  : Rand (Option Task.Actions) :=
  match tasks, vals with
  | [], _ => pure <| some { actions := [], deltaWitness := Anoma.DeltaWitness.empty }
  | task :: tasks', HList.cons vals' vals'' => do
    let try actions ← task.actions vals'
    let try rest ← makeActions tasks' vals''
    pure <| some <|
      { actions := actions.actions ++ rest.actions,
        deltaWitness := Anoma.DeltaWitness.compose actions.deltaWitness rest.deltaWitness }

def Task.composeMessages (tasks : List Task) (vals : HList (Products tasks)) : List SomeMessage :=
  match tasks, vals with
  | [], _ => []
  | task :: tasks', HList.cons vals' vals'' =>
    task.message vals' :: composeMessages tasks' vals''

def Task.composeParams (tasks : List Task) : Task.Parameters :=
  tasks |>.map (·.params) |> .concat

def Task.composeActions {α}
  (tasks : α → List Task)
  (mkAction : (a : α) → HList (Products (tasks a)) → Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
  : (Σ a : α, Task.composeParams (tasks a) |>.Product) → Rand (Option Task.Actions) :=
  fun ⟨a, vals⟩ => do
    let vals' := Task.Parameters.splitProducts vals
    let try actions ← Task.makeActions (tasks a) vals'
    let try (action, witness) ← mkAction a vals'
    pure <| some <|
      { actions := action :: actions.actions,
        deltaWitness := Anoma.DeltaWitness.compose witness actions.deltaWitness }

def Task.composeWithFetchAction
  (msg : SomeMessage)
  (objId : TypedObjectId)
  (tasks : Object objId.classLabel → List Task)
  (mkAction : (obj : Object objId.classLabel) → HList (Products (tasks obj)) → Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
  : Task :=
  { params := .fetch objId (composeParams ∘ tasks),
    message := fun _ => msg,
    actions := composeActions tasks mkAction }

def Task.composeWithFetch
  (msg : SomeMessage)
  (consumedObjectId : TypedObjectId)
  (tasks : Object consumedObjectId.classLabel → List Task)
  (createdObjects : Object consumedObjectId.classLabel → List CreatedObject)
  : Task :=
  let mkAction (obj : Object consumedObjectId.classLabel) (vals : HList (Products (tasks obj)))
    : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
    let try consumedObject := obj.toConsumedObject false
    let createdMessages := composeMessages (tasks obj) vals
    Action.create [consumedObject] (createdObjects obj) [msg] createdMessages
  Task.composeWithFetchAction msg consumedObjectId tasks mkAction

def Task.composeWithGenIdAction
  (message : ObjectId → SomeMessage)
  (tasks : ObjectId → List Task)
  (mkAction : (objId : ObjectId) → HList (Products (tasks objId)) → Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
  : Task :=
  { params := .genId (composeParams ∘ tasks),
    message := fun ⟨objId, _⟩ => message objId,
    actions := composeActions tasks mkAction }

def Task.composeWithGenId
  (message : ObjectId → SomeMessage)
  (tasks : ObjectId → List Task)
  (mkConsumedObject : ObjectId → SomeObject)
  (createdObjects : ObjectId → List CreatedObject)
  : Task :=
  let mkAction (objId : ObjectId) (vals : HList (Products (tasks objId)))
    : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
    let try consumedObject := mkConsumedObject objId |>.toConsumedObject true
    let createdMessages := composeMessages (tasks objId) vals
    Action.create [consumedObject] (createdObjects objId) [message objId] createdMessages
  Task.composeWithGenIdAction message tasks mkAction
