import Anoma.Resource

namespace Anoma

structure Logic.Args.{u, v, w} where
  self : Resource.{u, v}
  status : ConsumedCreated
  consumed : List Resource.{u, v}
  created : List Resource.{u, v}
  /-- `data` is the action's appData for self -/
  Data : SomeType.{w}
  data : Data.type

def Logic.Args.isConsumed (d : Logic.Args) := d.status.isConsumed

structure Logic.{u, v} where
  reference : LogicRef
  function : Logic.Args.{u, v} → Bool
