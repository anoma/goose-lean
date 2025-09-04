import Anoma
import AVM.Object
import AVM.Message
import AVM.Action
import AVM.Program.Parameters

namespace AVM

structure Task.Actions where
  actions : List Anoma.Action
  deltaWitness : Anoma.DeltaWitness

/-- Tasks are intermediate data structures used in the translation. Translating
  AVM message sends to Transactions first generates Tasks as an intermediate
  step. Tasks enable modularity of the translation – they are at the right
  level of abstraction to compose translations of different message sends,
  enabling nested method calls and subobjects. -/
structure Task.{u} : Type (u + 1) where
  /-- Task parameters - objects to fetch from the Anoma system and new object
    ids to generate. -/
  params : Program.Parameters
  /-- The message to send to the recipient. -/
  message : params.Product → Option SomeMessage
  /-- Task actions - actions to perform parameterised by fetched objects and new
    object ids. -/
  actions : params.Product → Rand (Option Task.Actions)
deriving Inhabited

def Task.absorbParams.{u} (params : Program.Parameters) (task : params.Product → Task.{u}) : Task.{u} :=
  { params := params.append (fun vals => (task vals).params),
    message := fun vals =>
      let ⟨vals1, vals2⟩ := Program.Parameters.splitProduct vals
      (task vals1).message vals2,
    actions := fun vals =>
      let ⟨vals1, vals2⟩ := Program.Parameters.splitProduct vals
      (task vals1).actions vals2 }

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
    (task.message vals' |>.toList) ++
      composeMessages tasks' vals''

def Task.composeParams (tasks : List Task) : Program.Parameters :=
  tasks |>.map (·.params) |> .concat

def Task.composeActions
  (tasks : List Task)
  (mkAction : HList (Products tasks) → Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
  (vals : (Task.composeParams tasks).Product)
  : Rand (Option Task.Actions) := do
  let vals' := Program.Parameters.splitProducts vals
  let try actions ← Task.makeActions tasks vals'
  let try (action, witness) ← mkAction vals'
  pure <| some <|
    { actions := action :: actions.actions,
      deltaWitness := Anoma.DeltaWitness.compose witness actions.deltaWitness }

def Task.composeWithAction
  (msg : Option SomeMessage)
  (tasks : List Task)
  (mkAction : HList (Products tasks) → Rand (Option (Anoma.Action × Anoma.DeltaWitness)))
  : Task :=
  { params := composeParams tasks,
    message := fun _ => msg,
    actions := composeActions tasks mkAction }

def Task.composeWithMessage
  (msg : SomeMessage)
  (tasks : List Task)
  (consumedObjs : List SomeConsumableObject)
  (createdObjects : List CreatedObject)
  : Task :=
  let mkAction (vals : HList (Products tasks))
    : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
    let try consumedObjects := consumedObjs.map (·.consume) |>.getSome
    let createdMessages := composeMessages tasks vals
    Action.create consumedObjects createdObjects [msg] createdMessages
  Task.composeWithAction msg tasks mkAction

def Task.compose (tasks : List Task) : Task :=
  let mkAction (vals : HList (Products tasks))
    : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
    let createdMessages := composeMessages tasks vals
    Action.create [] [] [] createdMessages
  Task.composeWithAction none tasks mkAction
