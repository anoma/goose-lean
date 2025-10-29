import Prelude
import Anoma.Resource
import Anoma.Program
import Anoma.Logic
import Anoma.Transaction
import AVM.Object
import AVM.Scope
import Mathlib.Control.Random

namespace Anoma.Program

structure RmState : Type 2 where
  gen : StdGen
  objects : Std.HashMap ObjectId Resource
  committed : Std.HashSet Commitment
  nullified : Std.HashSet Resource
  logics : Std.HashMap LogicRef LogicFunction

  logs : List String

structure SplitAction : Type 3 where
  consumed : List Resource
  created : List Resource

abbrev RmState.ini (logics : Std.HashMap LogicRef LogicFunction) (gen : StdGen := mkStdGen 0) : RmState :=
  { gen
    objects := ∅
    nullified := ∅
    committed := ∅
    logics
    logs := ∅ }

/-- The evaluation monad -/
abbrev RunM (a : Type 2) : Type 2 :=
  EStateM (Program.Error) RmState a

def logmsg (msg : String) : RunM PUnit :=
  modify (fun s => {s with logs := s.logs.cons msg})

def throw' {α : Type _} (e : Program.Error) : RunM α :=
  throw e

/-- checks that consumed and created resources of the same kind are balanced -/
def checkDelta (actions : List SplitAction) : RunM PUnit := do
  let consumed := actions.flatMap (·.consumed)
  let created := actions.flatMap (·.created)
  let mkMap (l : List Resource) : Std.HashMap Resource.Kind (List Resource) := l.groupByKey (·.kind)
  let consumedByKind := mkMap consumed
  let createdByKind := mkMap created
  let kinds : Std.HashSet Resource.Kind := Std.HashSet.ofList (consumedByKind.keys ++ createdByKind.keys)
  let getResourcesOfKind (m : Std.HashMap Resource.Kind (List Resource)) (k : Resource.Kind) : List Resource :=
    m.get? k |>.getD []
  let getQuantityOfKind (m : Std.HashMap Resource.Kind (List Resource)) (k : Resource.Kind) : Nat :=
    getResourcesOfKind m k |>.map (·.quantity) |>.sum
  for kind in kinds do
    let numConsumed := getQuantityOfKind consumedByKind kind
    let numCreated := getQuantityOfKind createdByKind kind
    if numConsumed == numCreated
    then pure .unit
    else throw' (.balanceCheck { consumed
                                 created
                                 kind
                                 kindCreated := getResourcesOfKind createdByKind kind
                                 kindConsumed := getResourcesOfKind consumedByKind kind })

def picks {A : Type u} (l : List A) : List (A × List A) :=
  List.finRange l.length |>.map (fun i => ⟨l.get i, l.eraseIdx i⟩)

def fetchLogic (ref : LogicRef) : RunM (LogicFunction) := do
  let s <- get
  match s.logics.get? ref with
  | none => throw' (.missingLogic ref)
  | some s => pure s

def storeLogic (ref : LogicRef) (f : LogicFunction) : RunM PUnit := do
  modify (fun s => {s with logics := s.logics.insert ref f})

def storeCreated (created : List Resource) : RunM PUnit := do
  let created := created.filter (·.ephemeral.not)
  for r in created do
    let try val : AVM.Object.Resource.SomeValue := tryCast r.value
    modify (fun s => {s with objects := s.objects.insert val.uid r
                             committed := s.committed.insert r.commitment})


def Action.split (a : Action) : SplitAction :=
  let units : List ComplianceUnit := a.complianceUnits
  let witnesses : List ComplianceWitness := units.map (·.witness)
  { consumed := witnesses.map (·.consumedResource)
    created := witnesses.map (·.createdResource) }


def runAction (a : SplitAction) : RunM PUnit := do
  let consumed : List Resource := a.consumed
  let created : List Resource := a.created
  let createdPicks := picks created
  let consumedPicks := picks consumed
  let checkLogic
        (self : Resource)
        (status : ConsumedCreated)
        (consumed' created' : List Resource) : RunM PUnit
        := do
        let args : Logic.Args :=
          { self
            status
            consumed := consumed'
            created := created'
            Data := ⟨Unit⟩
            data := .unit }
        let logic <- fetchLogic self.logicRef
        match logic args |>.eval with
        | none => pure .unit
        | some err => throw' (.logicFailed self.logicRef err)
  for (r, consumed') in consumedPicks do
    checkLogic r .Consumed consumed' created
  for (r, created') in createdPicks do
    checkLogic r .Created consumed created'
  storeCreated created
  -- TODO nullify consumed

def runTransaction (t : Transaction) : RunM PUnit := do
  let actions : List SplitAction := t.actions |>.map Action.split
  checkDelta actions
  for action in actions do
    runAction action

partial
def interpret : Program → RunM PUnit
  | .skip => pure .unit
  | .raise err => throw' err
  | .log msg next => do
    modify (fun s => {s with logs := s.logs.cons msg})
    interpret next
  | .tryCatch b handle next =>
      try do
        interpret b
        interpret next
      catch err => interpret (handle err)
  | .queryResource q next => do
    let s ← get
    match s.objects.get? q.uid with
    | .none => throw' (.storageError s!"object {q.uid} not in storage")
    | .some r => interpret (next r)
  | .submitTransaction t next => do
    runTransaction t
    interpret next
  | .withRandomGen next => do
    let s ← get
    let ⟨gen1, gen2⟩ := stdSplit s.gen
    set {s with gen := gen1}
    next gen2 |>.interpret

def eval
  {lab : AVM.Scope.Label}
  (scope : AVM.Scope lab)
  (p : Program)
  : EStateM.Result Program.Error RmState PUnit :=
  let logics := Std.HashMap.ofList (scope.logics.map fun l => ⟨l.reference, l.function⟩)
  interpret p |>.run (RmState.ini logics)

def run {lab : AVM.Scope.Label} (scope : AVM.Scope lab) (p : Program) : IO Unit := do
  let printLogs (logs : List String) : IO Unit := do
    if logs.isEmpty then IO.println "<no logs>" else pure Unit.unit
    for log in logs do
      IO.println log
  match eval scope p with
  | .ok _res s => do
    printLogs s.logs
    IO.println "success"
  | .error err s => do
    printLogs s.logs
    IO.println (repr err)
    IO.Process.exit 1
