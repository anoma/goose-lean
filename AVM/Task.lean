import Prelude
import Mathlib.Data.Prod.TProd
import Anoma
import AVM.Object
import AVM.Message
import AVM.Action

namespace AVM

structure Task.Actions where
  actions : List Anoma.Action
  deltaWitness : Anoma.DeltaWitness

inductive Task.Parameters where
  | empty
  | fetch (param : TypedObjectId) (rest : Object param.classLabel → Task.Parameters)
  | genId (rest : ObjectId → Task.Parameters)
deriving Inhabited

def Task.Parameters.Product (params : Task.Parameters) : Type :=
  match params with
  | .empty => PUnit
  | .fetch param rest =>
    Σ (obj : Object param.classLabel), Task.Parameters.Product (rest obj)
  | .genId rest =>
    Σ (objId : ObjectId), Task.Parameters.Product (rest objId)

def Task.Parameters.append (params1 : Task.Parameters) (params2 : params1.Product → Task.Parameters) : Task.Parameters :=
  match params1 with
  | .empty =>
    params2 PUnit.unit
  | .fetch p1 ps1 =>
    .fetch p1
      (fun obj => (ps1 obj).append (fun vals => params2 ⟨obj, vals⟩))
  | .genId ps1 =>
    .genId (fun objId => (ps1 objId).append (fun vals => params2 ⟨objId, vals⟩))

def Task.Parameters.concat (params : List Task.Parameters) : Task.Parameters :=
  match params with
  | [] => .empty
  | ps :: rest =>
    ps.append (fun _ => Task.Parameters.concat rest)

structure Task where
  /-- Task parameters - objects to fetch from the Anoma system. -/
  params : Task.Parameters
  /-- The message to send to the recipient. -/
  message : params.Product → SomeMessage
  /-- Task actions - actions to perform parameterised by fetched objects. -/
  actions : params.Product → Rand (Option Task.Actions)
deriving Inhabited

def Task.Parameters.splitProduct
  {params1 : Task.Parameters}
  {params2 : params1.Product → Task.Parameters}
  (vals : params1.append params2 |>.Product)
  : Σ (vals : params1.Product), (params2 vals).Product :=
  match params1 with
  | .empty => ⟨PUnit.unit, vals⟩
  | .fetch _ _ =>
    let ⟨obj, vals'⟩ := vals
    let ⟨vals1, vals2⟩ := splitProduct vals'
    ⟨⟨obj, vals1⟩, vals2⟩
  | .genId _ =>
    let ⟨objId, vals'⟩ := vals
    let ⟨vals1, vals2⟩ := splitProduct vals'
    ⟨⟨objId, vals1⟩, vals2⟩

def Task.Parameters.splitProducts
  {params : List Task.Parameters}
  (vals : Task.Parameters.concat params |>.Product)
  : HList (params.map Product) :=
  match params with
  | [] => HList.nil
  | _ :: ps =>
    let ⟨vals1, vals'⟩ := splitProduct vals
    let rest : HList (ps.map Product) := splitProducts vals'
    HList.cons vals1 rest

def Task.Parameters.Products (tasks : List Task) : List Type :=
  tasks.map (·.params) |> .map (·.Product)

def Task.Parameters.makeActions
  (tasks : List Task)
  (vals : HList (Parameters.Products tasks))
  : Rand (Option Task.Actions) :=
  match tasks, vals with
  | [], _ => pure <| some { actions := [], deltaWitness := Anoma.DeltaWitness.empty }
  | task :: tasks', HList.cons vals' vals'' => do
    let try actions ← task.actions vals'
    let try rest ← makeActions tasks' vals''
    pure <| some <|
      { actions := actions.actions ++ rest.actions,
        deltaWitness := Anoma.DeltaWitness.compose actions.deltaWitness rest.deltaWitness }

def Task.composeMessages (tasks : List Task) (vals : HList (Parameters.Products tasks)) : List SomeMessage :=
  match tasks, vals with
  | [], _ => []
  | task :: tasks', HList.cons vals' vals'' =>
    task.message vals' :: composeMessages tasks' vals''

def Task.composeParams (tasks : List Task) : Task.Parameters :=
  tasks |>.map (·.params) |> .concat

def Task.composeActions {α}
  (tasks : α → List Task)
  (mkAction : (a : α) → HList (Parameters.Products (tasks a)) → Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
  : (Σ a : α, Task.composeParams (tasks a ) |>.Product) → Rand (Option Task.Actions) :=
  fun ⟨obj, vals⟩ => do
    let vals' := Task.Parameters.splitProducts vals
    let try actions ← Task.Parameters.makeActions (tasks obj) vals'
    let try (action, witness) ← mkAction obj vals'
    pure <| some <|
      { actions := action :: actions.actions,
        deltaWitness := Anoma.DeltaWitness.compose witness actions.deltaWitness }

def Task.composeWithFetchAction
  (msg : SomeMessage)
  (objId : TypedObjectId)
  (tasks : Object objId.classLabel → List Task)
  (mkAction : (obj : Object objId.classLabel) → HList (Parameters.Products (tasks obj)) → Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
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
  let mkAction (obj : Object consumedObjectId.classLabel) (vals : HList (Parameters.Products (tasks obj)))
    : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
    let try consumedObject := obj.toConsumedObject false
    let createdMessages := composeMessages (tasks obj) vals
    Action.create [consumedObject] (createdObjects obj) [msg] createdMessages
  Task.composeWithFetchAction msg consumedObjectId tasks mkAction

def Task.composeWithGenIdAction
  (message : ObjectId → SomeMessage)
  (tasks : ObjectId → List Task)
  (mkAction : (objId : ObjectId) → HList (Parameters.Products (tasks objId)) → Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
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
  let mkAction (objId : ObjectId) (vals : HList (Parameters.Products (tasks objId)))
    : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
    let try consumedObject := mkConsumedObject objId |>.toConsumedObject true
    let createdMessages := composeMessages (tasks objId) vals
    Action.create [consumedObject] (createdObjects objId) [message objId] createdMessages
  Task.composeWithGenIdAction message tasks mkAction
