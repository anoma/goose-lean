import Anoma
import AVM.Task

namespace AVM.Task

/-- Creates an Anoma Transaction for a given Task. -/
def toTransaction (task : Task) (objs : Task.Parameter.Product task.params) : Rand (Option Anoma.Transaction) := do
  let (action, witness) ← Action.create [] [] [] [task.message]
  let try actions : Task.Actions ← task.actions objs
  let witness' : Anoma.DeltaWitness :=
    Anoma.DeltaWitness.compose actions.deltaWitness witness
  let acts : List Anoma.Action := action :: actions.actions
  pure <|
    some
      { actions := acts,
        deltaProof := Anoma.Transaction.generateDeltaProof witness' acts }

private def fetchObjects (params : List Task.Parameter) (cont : Task.Parameter.Product params → Anoma.Program) : Anoma.Program :=
  match params with
  | [] => cont PUnit.unit
  | p :: ps =>
    fetchObjects ps (fun objs' =>
      Anoma.Program.queryResource (Anoma.Program.ResourceQuery.queryByObjectId p.uid) (fun res =>
        let try obj : Object p.classLabel := Object.fromResource res
            failwith Anoma.Program.raise <| Anoma.Program.Error.typeError ("expected object of class " ++ p.classLabel.name);
        cont (obj, objs')))

/-- Creates an Anoma Program for a given Task. -/
def toProgram (task : Task) : Anoma.Program :=
  let cont (objs : Task.Parameter.Product task.params) : Anoma.Program :=
    Anoma.Program.withRandOption do
      let try tx : Anoma.Transaction ← task.toTransaction objs
      pure <| Anoma.Program.submitTransaction tx Anoma.Program.skip
  fetchObjects task.params cont
