import AVM.Ecosystem.Label
import AVM.Object.Consumed

namespace AVM

inductive DeconstructionKind : Type where
  /-- Will be consumed and automatically balanced with an ephemeral resource -/
  | Destroyed
  /-- Will be consumed. It is the responsibility of the user to balance disassembled objects with assembled objects -/
  | Disassembled
  deriving BEq

structure FunctionResult {lab : Ecosystem.Label} (functionId : lab.FunctionId) : Type (u + 1) where
  /-- List of assembled objects. Assembled objects will be created.
      It is the responsibility of the user to ensure that
      assembled objects balance with the object arguments that are disassembled -/
  assembled : List SomeObject
  /-- List of destroyed objects. Destroyed objects will be balanced with automatically generated ephemeral resources -/
  destroyed : List SomeConsumableObject
  /-- List of constructed objects. Constructed objects will be balanced with automatically generated ephemeral resources -/
  constructed : List SomeObject
  /-- For each object argument we specify its usage. See `Usage`.
  Note that if `argUsage arg = .Destroyed`, then the object that corresponds to `arg` should *not* be put in the destroyed list -/
  argDeconstruction : functionId.ObjectArgNames → DeconstructionKind

def FunctionResult.numSelvesDestroyed
  {lab : Ecosystem.Label}
  {functionId : lab.FunctionId}
  (res : FunctionResult functionId)
  : Nat :=
  functionId.objectArgNames.countP (fun a => res.argDeconstruction a == .Destroyed)

structure Function {lab : Ecosystem.Label} (functionId : lab.FunctionId) where
  /-- Computes the result of a function call. See `FunctionResult`. -/
  body (selves : functionId.Selves) (args : functionId.Args.type) : FunctionResult functionId
  /-- Extra function logic. -/
  invariant (selves : functionId.Selves) (args : functionId.Args.type) : Bool
