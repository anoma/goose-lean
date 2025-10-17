import Anoma.Resource

namespace Anoma

structure Logic.Args.{u, v} : Type (max u v + 1) where
  self : Resource.{u, v}
  status : ConsumedCreated
  consumed : List Resource.{u, v}
  created : List Resource.{u, v}
  /-- `data` is the action's appData for self -/
  Data : SomeType.{0}
  data : Data.type

def Logic.Args.isConsumed (d : Logic.Args) := d.status.isConsumed

abbrev LogicFunction.{u, v} : Type (max u v + 1) := Logic.Args.{u, v} → Bool

structure Logic.{u, v} where
  reference : LogicRef
  function : LogicFunction.{u, v}
