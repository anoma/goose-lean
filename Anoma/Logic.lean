import Anoma.Resource

namespace Anoma

structure Logic.Args : Type 2 where
  self : Resource
  status : ConsumedCreated
  consumed : List Resource
  created : List Resource
  /-- `data` is the action's appData for self -/
  Data : SomeType.{0}
  data : Data.type

def Logic.Args.isConsumed (d : Logic.Args) := d.status.isConsumed

abbrev LogicM : Type := Except String Unit

abbrev LogicM.true : LogicM := pure .unit

def LogicFunction : Type 2 := Logic.Args → LogicM

structure Logic where
  reference : LogicRef
  function : LogicFunction
