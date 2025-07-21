import AVM.Ecosystem.Label

namespace AVM

structure Function {lab : Ecosystem.Label} (functionId : lab.FunctionId) where
  /-- Objects created in the function call. -/
  created (selfs : functionId.Selves) (args : functionId.Args.type) : List SomeObject
  /-- Extra function logic. -/
  invariant (selfs : functionId.Selves) (args : functionId.Args.type) : Bool
