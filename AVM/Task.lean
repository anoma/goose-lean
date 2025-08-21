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
  | nil
  | cons (param : TypedObjectId) (rest : Object param.classLabel → Task.Parameters)
deriving Inhabited

def Task.Parameters.Product (params : Task.Parameters) : Type :=
  match params with
  | Task.Parameters.nil => PUnit
  | Task.Parameters.cons param rest =>
    Σ (obj : Object param.classLabel), Task.Parameters.Product (rest obj)

def Task.Parameters.append (params1 : Task.Parameters) (params2 : params1.Product → Task.Parameters) : Task.Parameters :=
  match params1 with
  | Task.Parameters.nil =>
    params2 PUnit.unit
  | Task.Parameters.cons p1 ps1 =>
    Task.Parameters.cons
      p1
      (fun obj => (ps1 obj).append (fun objs => params2 ⟨obj, objs⟩))

def Task.Parameters.concat (params : List Task.Parameters) : Task.Parameters :=
  match params with
  | [] => Task.Parameters.nil
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
  (objs : params1.append params2 |>.Product)
  : Σ (objs : params1.Product), (params2 objs).Product :=
  match params1 with
  | nil => ⟨PUnit.unit, objs⟩
  | cons _ _ =>
    let ⟨obj, objs'⟩ := objs
    let ⟨objs1, objs2⟩ := splitProduct objs'
    ⟨⟨obj, objs1⟩, objs2⟩

def Task.Parameters.splitProducts
  {params : List Task.Parameters}
  (objs : Task.Parameters.concat params |>.Product)
  : HList (params.map Product) :=
  match params with
  | [] => HList.nil
  | _ :: ps =>
    let ⟨objs1, objs'⟩ := splitProduct objs
    let rest : HList (ps.map Product) := splitProducts objs'
    HList.cons objs1 rest

def Task.Parameter.makeActions
  (tasks : List Task)
  (objs : HList (List.map Task.Parameters.Product (tasks.map (·.params))))
  : Rand (Option Task.Actions) :=
  match tasks, objs with
  | [], _ => pure <| some { actions := [], deltaWitness := Anoma.DeltaWitness.empty }
  | task :: tasks', HList.cons objs' objs'' => do
    let try actions ← task.actions objs'
    let try rest ← makeActions tasks' objs''
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
    actions := fun objs => do
      let objs' := Task.Parameters.splitProducts objs
      let try actions ← Task.Parameter.makeActions tasks objs'
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

def Task.composeWithParamAction
  (msg : SomeMessage)
  (param : TypedObjectId)
  (tasks : Object param.classLabel → List Task)
  (mkAction : Object param.classLabel → Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
  : Task :=
  { params := Task.Parameters.cons param fun obj => tasks obj |>.map (·.params) |> .concat,
    message := msg,
    actions := fun ⟨obj, objs⟩ => do
      let objs' := Task.Parameters.splitProducts objs
      let try actions ← Task.Parameter.makeActions (tasks obj) objs'
      let try (action, witness) ← mkAction obj
      pure <| some <|
        { actions := action :: actions.actions,
          deltaWitness := Anoma.DeltaWitness.compose witness actions.deltaWitness } }

def Task.composeWithParam
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
  Task.composeWithParamAction msg consumedObjectId tasks mkAction
