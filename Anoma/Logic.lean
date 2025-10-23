import Anoma.Resource

namespace Anoma

inductive Logic.Error : Type where
  | rawError (pos : FilePosition)
  | custom (pos : FilePosition) (msg : String)
  -- | rawError

instance : Repr Logic.Error where
  reprPrec e _ :=
    match e with
    | .rawError p => repr p
    | .custom p msg => s!"{repr p}: {msg}"

structure Logic.Args : Type 2 where
  self : Resource
  status : ConsumedCreated
  consumed : List Resource
  created : List Resource
  /-- `data` is the action's appData for self -/
  Data : SomeType.{0}
  data : Data.type

def Logic.Args.isConsumed (d : Logic.Args) := d.status.isConsumed

abbrev LogicM : Type := Except Logic.Error Unit

abbrev LogicM.true : LogicM := pure .unit

def LogicFunction : Type 2 := Logic.Args → LogicM

structure Logic where
  reference : LogicRef
  function : LogicFunction
