import Prelude
import Mathlib.Data.Prod.TProd
import Anoma
import AVM.Object
import AVM.Message
import AVM.Action

namespace AVM

structure Task.Parameter where
  uid : ObjectId
  classLabel : Class.Label

def Task.Parameter.Product (params : List Task.Parameter) : Type :=
  List.TProd (fun p : Task.Parameter => Object p.classLabel) params

structure Task where
  /-- Task parameters - objects to fetch from the Anoma system. -/
  params : List Task.Parameter
  /-- The message to send to the recipient. -/
  message : SomeMessage
  /-- Task actions - actions to perform parameterised by fetched objects. -/
  actions : Task.Parameter.Product params → List Anoma.Action

def Task.Parameter.splitProduct
  {params1 params2 : List Task.Parameter}
  (objs : Task.Parameter.Product (params1 ++ params2))
  : Task.Parameter.Product params1 × Task.Parameter.Product params2 :=
  match params1 with
  | [] => (PUnit.unit, objs)
  | p1 :: ps1 =>
    let (obj, objs') : Object p1.classLabel × Product (ps1 ++ params2) := objs
    let (objs1, objs2) : Product ps1 × Product params2 := splitProduct objs'
    ((obj, objs1), objs2)

def Task.Parameter.splitProducts
  {params : List (List Task.Parameter)}
  (objs : Task.Parameter.Product params.flatten)
  : HList (params.map Task.Parameter.Product) :=
  match params with
  | [] => HList.nil
  | p :: ps =>
    let (objs1, objs') : Product p × Product ps.flatten := splitProduct objs
    let rest : HList (ps.map Task.Parameter.Product) := splitProducts objs'
    HList.cons objs1 rest

def Task.Parameter.makeActions
  (tasks : List Task)
  (objs : HList (List.map Task.Parameter.Product (tasks.map (·.params))))
  : List Anoma.Action :=
  match tasks, objs with
  | [], _ => []
  | task :: tasks', HList.cons objs' objs'' =>
    let actions := task.actions objs'
    actions ++ makeActions tasks' objs''

def Task.composeWithAction
  (tasks : List Task)
  (msg : SomeMessage)
  (action : Anoma.Action)
  : Task :=
  let lparams : List (List Task.Parameter) := tasks.map (·.params)
  { params := lparams.flatten,
    message := msg,
    actions := fun objs =>
      let objs' := Task.Parameter.splitProducts objs
      action :: Task.Parameter.makeActions tasks objs' }

def Task.compose
  (tasks : List Task)
  (msg : SomeMessage)
  (consumedObjects : List SomeConsumedObject)
  (createdObjects : List CreatedObject)
  : Rand (Task × Anoma.DeltaWitness) := do
  let (action, witness) ← Action.create consumedObjects createdObjects [msg] (tasks.map (·.message))
  let task := Task.composeWithAction tasks msg action
  pure (task, witness)

/-- Creates an Anoma Transaction for a given Task. -/
def Task.toTransaction (task : Task) (witness : Anoma.DeltaWitness) (objs : Task.Parameter.Product task.params) : Rand Anoma.Transaction := do
  let (action, witness') ← Action.create [] [] [task.message] []
  let witness'' : Anoma.DeltaWitness :=
    Anoma.DeltaWitness.compose witness witness'
  let actions : List Anoma.Action := action :: task.actions objs
  pure <|
    { actions := actions,
      deltaProof := Anoma.Transaction.generateDeltaProof witness'' actions }
