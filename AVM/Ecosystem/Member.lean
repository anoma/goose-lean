import AVM.Ecosystem.Label

namespace AVM

structure Function {lab : EcosystemLabel} (functionId : lab.FunctionId) where
  /-- Objects created in the function call. -/
  created (selfs : functionId.Selfs) (args : functionId.Args.type) : List SomeObject
  /-- Extra function logic. -/
  invariant (selfs : functionId.Selfs) (args : functionId.Args.type) : Bool
