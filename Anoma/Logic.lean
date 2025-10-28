import Anoma.Resource

namespace Anoma

inductive LogicM.Error : Type where
  | onlyPosition (pos : FilePosition)
  | custom (pos : FilePosition) (msg : String)

instance : Repr LogicM.Error where
  reprPrec e _ :=
    match e with
    | .onlyPosition p => repr p
    | .custom p msg => s!"{repr p}\n{msg}"

structure Logic.Args : Type 2 where
  self : Resource
  status : ConsumedCreated
  consumed : List Resource
  created : List Resource
  /-- `data` is the action's appData for self -/
  Data : SomeType.{0}
  data : Data.type

def Logic.Args.isConsumed (d : Logic.Args) := d.status.isConsumed

abbrev LogicM : Type := Except LogicM.Error Unit

abbrev LogicM.true : LogicM := pure .unit

def LogicFunction : Type 2 := Logic.Args → LogicM

structure Logic where
  reference : LogicRef
  function : LogicFunction
