import Anoma
import AVM.Task

namespace AVM.Task

/-- Creates an Anoma Transaction for a given Task. -/
def toTransaction (task : Task) (objs : task.params.Product) : Rand (Option Anoma.Transaction) := do
  let (action, witness) ← Action.create [] [] [] [task.message]
  let try actions : Task.Actions ← task.actions objs
  let witness' : Anoma.DeltaWitness :=
    Anoma.DeltaWitness.compose actions.deltaWitness witness
  let acts : List Anoma.Action := action :: actions.actions
  pure <|
    some
      { actions := acts,
        deltaProof := Anoma.Transaction.generateDeltaProof witness' acts }

private def fetchObjects (params : Task.Parameters) (cont : params.Product → Anoma.Program) : Anoma.Program :=
  match params with
  | .nil => cont PUnit.unit
  | .cons p ps =>
    Anoma.Program.queryResource (Anoma.Program.ResourceQuery.queryByObjectId p.uid) (fun res =>
      let try obj : Object p.classLabel := Object.fromResource res
          failwith Anoma.Program.raise <| Anoma.Program.Error.typeError ("expected object of class " ++ p.classLabel.name);
      fetchObjects (ps obj) (fun objs' => cont ⟨obj, objs'⟩))

/-- Creates an Anoma Program for a given Task. -/
def toProgram (task : Task) : Anoma.Program :=
  let cont (objs : task.params.Product) : Anoma.Program :=
    Anoma.Program.withRandOption do
      let try tx : Anoma.Transaction ← task.toTransaction objs
      pure <| Anoma.Program.submitTransaction tx Anoma.Program.skip
  fetchObjects task.params cont

def toProgramRand (task : Rand Task) : Anoma.Program :=
  Anoma.Program.withRandomGen fun g =>
    let (task', g') := task.run (ULift.up g)
    (task'.toProgram, ULift.down g')

def toProgramRandOption (task : Rand (Option Task)) : Anoma.Program :=
  Anoma.Program.withRandomGen fun g =>
    let (task?, g') := task.run (ULift.up g)
    match task? with
    | none => (Anoma.Program.raise Anoma.Program.Error.userError, ULift.down g')
    | some task' => (task'.toProgram, ULift.down g')
