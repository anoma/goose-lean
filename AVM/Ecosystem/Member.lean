import AVM.Ecosystem.Label
import AVM.Object.Consumable

namespace AVM

structure FunctionResult : Type (u + 1) where
  created : List SomeObject
  destroyed : List SomeConsumableObject

structure Function {lab : Ecosystem.Label} (functionId : lab.FunctionId) where
  /-- Objects created in the function call. -/
  body (selves : functionId.Selves) (args : functionId.Args.type) : FunctionResult
  /-- Extra function logic. -/
  invariant (selves : functionId.Selves) (args : functionId.Args.type) : Bool
