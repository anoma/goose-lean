import AVM.Ecosystem.Label
import AVM.Object.Consumable

namespace AVM

structure FunctionResult : Type (u + 1) where
  /-- List of created objects -/
  created : List SomeObject
  /-- List of objects destroyed. Destroyed elements will be balanced with automatically generated ephemeral resources -/
  destroyed : List SomeConsumableObject
  constructed : List SomeObject

structure Function {lab : Ecosystem.Label} (functionId : lab.FunctionId) where
  /-- Computes the result of a function call. See `FunctionResult`. -/
  body (selves : functionId.Selves) (args : functionId.Args.type) : FunctionResult
  /-- Extra function logic. -/
  invariant (selves : functionId.Selves) (args : functionId.Args.type) : Bool
