import Anoma
import AVM.Task

namespace AVM.Task

/-- Creates an Anoma Transaction for a given Task. -/
def toTransaction (task : Task) (vals : task.params.Product) : Rand (Option Anoma.Transaction) := do
  match task.message vals with
  | none =>
    let try actions : Task.Actions ← task.actions vals
    pure <| some <|
      { actions := actions.actions,
        deltaProof := Anoma.Transaction.generateDeltaProof actions.deltaWitness actions.actions }
  | some msg =>
    let (action, witness) ← Action.create [] [] [] [msg]
    let try actions : Task.Actions ← task.actions vals
    let witness' : Anoma.DeltaWitness :=
      Anoma.DeltaWitness.compose witness actions.deltaWitness
    let acts : List Anoma.Action := action :: actions.actions
    pure <| some <|
      { actions := acts,
        deltaProof := Anoma.Transaction.generateDeltaProof witness' acts }

private def resolveParameters (params : Task.Parameters) (cont : params.Product → Anoma.Program) : Anoma.Program :=
  match params with
  | .empty => cont PUnit.unit
  | .fetch p ps =>
    Anoma.Program.queryResource (Anoma.Program.ResourceQuery.queryByObjectId p.uid) (fun res =>
      let try obj : Object p.classLabel := Object.fromResource res
          failwith Anoma.Program.raise <| Anoma.Program.Error.typeError ("expected object of class " ++ p.classLabel.name)
      resolveParameters (ps obj) (fun vals => cont ⟨obj, vals⟩))
  | .genId ps =>
    Anoma.Program.genObjectId (fun objId =>
      resolveParameters (ps objId) (fun vals => cont ⟨objId, vals⟩))

/-- Creates an Anoma Program for a given Task. -/
def toProgram (task : Task) : Anoma.Program :=
  let cont (vals : task.params.Product) : Anoma.Program :=
    Anoma.Program.withRandOption do
      let try tx : Anoma.Transaction ← task.toTransaction vals
      pure <| Anoma.Program.submitTransaction tx Anoma.Program.skip
  resolveParameters task.params cont

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
