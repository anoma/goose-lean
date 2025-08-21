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
  message : SomeMessage
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

def Task.Parameter.makeActions
  (tasks : List Task)
  (vals : HList (List.map Task.Parameters.Product (tasks.map (·.params))))
  : Rand (Option Task.Actions) :=
  match tasks, vals with
  | [], _ => pure <| some { actions := [], deltaWitness := Anoma.DeltaWitness.empty }
  | task :: tasks', HList.cons vals' vals'' => do
    let try actions ← task.actions vals'
    let try rest ← makeActions tasks' vals''
    pure <| some <|
      { actions := actions.actions ++ rest.actions,
        deltaWitness := Anoma.DeltaWitness.compose actions.deltaWitness rest.deltaWitness }

def Task.composeWithAction
  (tasks : List Task)
  (msg : SomeMessage)
  (mkAction : Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
  : Task :=
  let lparams : List Task.Parameters := tasks.map (·.params)
  { params := .concat lparams,
    message := msg,
    actions := fun vals => do
      let vals' := Task.Parameters.splitProducts vals
      let try actions ← Task.Parameter.makeActions tasks vals'
      let try (action, witness) ← mkAction
      pure <| some <|
        { actions := action :: actions.actions,
          deltaWitness := Anoma.DeltaWitness.compose witness actions.deltaWitness } }

def Task.compose
  (tasks : List Task)
  (msg : SomeMessage)
  (consumedObject : SomeConsumedObject)
  (createdObjects : List CreatedObject)
  : Task :=
  let createdMessages := tasks.map (·.message)
  Action.create [consumedObject] createdObjects [msg] createdMessages |>
    Task.composeWithAction tasks msg

def Task.composeWithFetchAction
  (msg : SomeMessage)
  (objId : TypedObjectId)
  (tasks : Object objId.classLabel → List Task)
  (mkAction : Object objId.classLabel → Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
  : Task :=
  { params := .fetch objId fun obj => tasks obj |>.map (·.params) |> .concat,
    message := msg,
    actions := fun ⟨obj, vals⟩ => do
      let vals' := Task.Parameters.splitProducts vals
      let try actions ← Task.Parameter.makeActions (tasks obj) vals'
      let try (action, witness) ← mkAction obj
      pure <| some <|
        { actions := action :: actions.actions,
          deltaWitness := Anoma.DeltaWitness.compose witness actions.deltaWitness } }

def Task.composeWithFetch
  (msg : SomeMessage)
  (consumedObjectId : TypedObjectId)
  (tasks : Object consumedObjectId.classLabel → List Task)
  (createdObjects : Object consumedObjectId.classLabel → List CreatedObject)
  : Task :=
  let mkAction (consumedObj : Object consumedObjectId.classLabel)
    : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
    let consumable : ConsumableObject consumedObjectId.classLabel :=
        { object := consumedObj
          ephemeral := false }
    let try consumedObject : ConsumedObject consumedObjectId.classLabel := consumable.consume
    let createdMessages := (tasks consumedObj).map (·.message)
    Action.create [consumedObject] (createdObjects consumedObj) [msg] createdMessages
  Task.composeWithFetchAction msg consumedObjectId tasks mkAction
