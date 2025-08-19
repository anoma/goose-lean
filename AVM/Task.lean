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

structure Task.Actions where
  actions : List Anoma.Action
  deltaWitness : Anoma.DeltaWitness

structure Task where
  /-- Task parameters - objects to fetch from the Anoma system. -/
  params : List Task.Parameter
  /-- The message to send to the recipient. -/
  message : SomeMessage
  /-- Task actions - actions to perform parameterised by fetched objects. -/
  actions : Task.Parameter.Product params → Rand (Option Task.Actions)

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
  : Rand (Option Task.Actions) :=
  match tasks, objs with
  | [], _ => pure <| some { actions := [], deltaWitness := Anoma.DeltaWitness.empty }
  | task :: tasks', HList.cons objs' objs'' => do
    let try actions ← task.actions objs'
    let try rest ← makeActions tasks' objs''
    pure <|
      some
        { actions := actions.actions ++ rest.actions,
          deltaWitness := Anoma.DeltaWitness.compose actions.deltaWitness rest.deltaWitness }

def Task.composeWithAction
  (tasks : List Task)
  (msg : SomeMessage)
  (action : Anoma.Action)
  (witness : Anoma.DeltaWitness)
  : Rand (Option Task) :=
  let lparams : List (List Task.Parameter) := tasks.map (·.params)
  pure <|
    some
      { params := lparams.flatten,
        message := msg,
        actions := fun objs => do
          let objs' := Task.Parameter.splitProducts objs
          let try actions ← Task.Parameter.makeActions tasks objs'
          pure <|
            some
              { actions := action :: actions.actions,
                deltaWitness := Anoma.DeltaWitness.compose witness actions.deltaWitness } }

def Task.compose
  (tasks : List Task)
  (msg : SomeMessage)
  (consumedObject : SomeConsumedObject)
  (createdObjects : List CreatedObject)
  : Rand (Option Task) := do
  let createdMessages := tasks.map (·.message)
  let (action, witness) ← Action.create [consumedObject] createdObjects [msg] createdMessages
  Task.composeWithAction tasks msg action witness
