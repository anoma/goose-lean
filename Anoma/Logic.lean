import Anoma.Resource

namespace Anoma

structure LogicM.Error : Type where
  stackTrace : List String
  position : FilePosition
  reason : String

def LogicM.Error.onlyPosition (position : FilePosition) : LogicM.Error where
  position
  stackTrace := []
  reason := "<no explicit reason>"

def LogicM.Error.custom (position : FilePosition) (reason : String) : LogicM.Error where
  position
  stackTrace := []
  reason

instance : Repr LogicM.Error where
  reprPrec e _ :=
    s!"Error at {repr e.position}
      Reason:\n{e.reason}
      Trace:\n{e.stackTrace.unlines}"

structure Logic.Args : Type 2 where
  self : Resource
  status : ConsumedCreated
  consumed : List Resource
  created : List Resource
  /-- `data` is the action's appData for self -/
  Data : SomeType.{0}
  data : Data.type

-- The StackTrace is only used in the error message. It should never be used to
-- branch on a computation.
abbrev LogicM.StackTrace := List String

def Logic.Args.isConsumed (d : Logic.Args) := d.status.isConsumed

abbrev LogicM : Type := EStateM LogicM.Error LogicM.StackTrace Unit

abbrev LogicM.true : LogicM := pure .unit

abbrev LogicM.eval (l : LogicM) : Option LogicM.Error :=
  match l.run ∅ with
  | .error e _ => some e
  | .ok _ _ => none

abbrev LogicM.withTrace (here : FilePosition) (str : String) (l : LogicM) : LogicM := do
  let old ← get
  set (s!"{repr here}: {str}" :: old)
  l
  set old

abbrev LogicM.isOk (l : LogicM) : Bool := l.eval.isNone

def LogicM.throw (position : FilePosition) (reason : String) : LogicM := do
  let s ← get
  MonadExcept.throw
    { reason
      position
      stackTrace := s.reverse }

def LogicFunction : Type 2 := Logic.Args → LogicM

structure Logic where
  reference : LogicRef
  function : LogicFunction
