import Prelude
import Anoma.Resource
import Anoma.Program
import Anoma.Logic
import Anoma.Transaction
import AVM.Object
import AVM.Scope
import Mathlib.Control.Random

namespace Anoma.Program

structure RmState.{u, v} : Type (max u v + 1) where
  gen : StdGen
  objects : Std.HashMap ObjectId Resource.{u, v}
  commited : Std.HashSet Commitment
  nullified : Std.HashSet Resource.{u, v}
  logics : Std.HashMap LogicRef LogicFunction.{u, v}

  logs : List String

abbrev RmState.ini (logics : Std.HashMap LogicRef LogicFunction) (gen : StdGen := mkStdGen 0) : RmState :=
  { gen
    objects := ∅
    nullified := ∅
    commited := ∅
    logics
    logs := ∅ }

/-- The evaluation monad -/
abbrev RunM.{u, v} (a : Type (max u v + 1)) : Type (max u v + 1) :=
  EStateM (ULift Program.Error) (ULift RmState.{u, v}) a

def modify' (f : RmState → RmState) : RunM PUnit :=
  modify (fun s => ULift.up (f s.down))

def get'.{u, v} : RunM.{u, v} RmState.{u, v} :=
  (·.down) <$> get

def set' (s : RmState) : RunM PUnit :=
  set (ULift.up s)

def throw' {α : Type _} (e : Program.Error) : RunM α :=
  throw (ULift.up e)

/-- checks that consumed and created resources of the same kind are balanced -/
def checkDelta.{u, v} (consumed created : List Resource.{u, v}) : RunM PUnit := do
  let mkMap (l : List Resource.{u, v}) : Std.HashMap Resource.Kind.{v} (List Resource.{u, v}) := l.groupByKey (·.kind)
  let consumedByKind := mkMap consumed
  let createdByKind := mkMap created
  let kinds : Std.HashSet Resource.Kind.{v} := Std.HashSet.ofList (consumedByKind.keys ++ createdByKind.keys)
  let getQuantityOfKind (m : Std.HashMap Resource.Kind.{v} (List Resource.{u, v})) (k : Resource.Kind.{v}) : Nat :=
    m.get? k |>.getD [] |>.map (·.quantity) |>.sum
  for kind in kinds do
    let numConsumed := getQuantityOfKind consumedByKind kind
    let numCreated := getQuantityOfKind createdByKind kind
    if numConsumed == numCreated
    then pure .unit
    -- else throw' (.balanceCheck s!"numConsumed: {numConsumed}/{consumed.length}, numCreated: {numCreated}/{created.length}")
    else pure .unit

def picks {A : Type u} (l : List A) : List (A × List A) :=
  List.finRange l.length |>.map (fun i => ⟨l.get i, l.eraseIdx i⟩)

def fetchLogic.{u, v} (ref : LogicRef) : RunM.{u, v} (LogicFunction.{u, v}) := do
  let s <- get'
  match s.logics.get? ref with
  | none => throw' (.missingLogic ref)
  | some s => pure s

def storeLogic (ref : LogicRef) (f : LogicFunction) := do
  modify' (fun s => {s with logics := s.logics.insert ref f})

def storeCreated (created : List Resource) : RunM PUnit := do
  let created := created.filter (·.ephemeral.not)
  for r in created do
    dbgTrace s!"created" (fun _ =>
    let try val : AVM.Object.Resource.SomeValue := tryCast r.value
    dbgTrace s!"hi: {val.uid}" (fun _ =>
    modify' (fun s => {s with objects := s.objects.insert val.uid r
                              commited := s.commited.insert r.commitment})))

def runAction (a : Action) : RunM PUnit := do
  let units : List ComplianceUnit := a.complianceUnits
  let witnesses : List ComplianceWitness := units.map (·.witness)
  let consumed : List Resource := witnesses.map (·.consumedResource)
  let created : List Resource := witnesses.map (·.createdResource)
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
        if logic args
        then pure .unit
        else throw' .logicFailed
  checkDelta consumed created
  for (r, consumed') in consumedPicks do
    checkLogic r .Consumed consumed' created
  for (r, created') in createdPicks do
    checkLogic r .Created consumed created'
  storeCreated created
  -- TODO nullify consumed

def logmsg (msg : String) : RunM PUnit :=
  modify' (fun s => {s with logs := s.logs.cons msg})

def runTransaction (t : Transaction) : RunM PUnit := do
  let actions : List Action := t.actions
  logmsg "runtrans2"
  for action in actions do
    runAction action

partial
def interpret : Program → RunM PUnit
  | .skip => pure .unit
  | .raise err => throw' err
  | .log msg next => do
    modify' (fun s => {s with logs := s.logs.cons msg})
    interpret next
  | .tryCatch b handle next =>
      try do
        interpret b
        interpret next
      catch err => interpret (handle (ULift.down err))
  | .queryResource q next => do
    let s ← get
    match s.down.objects.get? q.uid with
    | .none => throw' (.storageError s!"object {q.uid} not in storage")
    | .some r => interpret (next r)
  | .submitTransaction t next => do
    runTransaction t
    interpret next
  | .withRandomGen next => do
    let s ← get'
    let ⟨gen1, gen2⟩ := stdSplit s.gen
    set' {s with gen := gen1}
    next gen2 |>.interpret



def eval {lab : AVM.Scope.Label} (scope : AVM.Scope lab) (p : Program) : EStateM.Result (ULift Program.Error) (ULift RmState) PUnit :=
  let logics := Std.HashMap.ofList (scope.logics.map fun l => ⟨l.reference, l.function⟩)
  interpret p |>.run (ULift.up (RmState.ini logics))

def run {lab : AVM.Scope.Label} (scope : AVM.Scope lab) (p : Program) : IO Unit := do
  let printLogs (logs : List String) : IO Unit := do
    if logs.isEmpty then IO.println "<no logs>" else pure Unit.unit
    for log in logs do
      IO.println log
  match eval scope p with
  | .ok _res s => do
    printLogs s.down.logs
    IO.println "success"
  | .error err s => do
    printLogs s.down.logs
    IO.println "error"
    IO.println (repr err.down)
