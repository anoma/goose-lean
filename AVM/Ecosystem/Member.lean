import AVM.Program
import AVM.Ecosystem.Label
import AVM.Object.Consumed

namespace AVM

inductive DeconstructionKind : Type where
  /-- Will be consumed and automatically balanced with an ephemeral resource -/
  | Destroyed
  /-- Will be consumed. It is the responsibility of the user to balance disassembled objects with assembled objects -/
  | Disassembled
  deriving BEq

-- Question: Show it be allowed that there exists a disassembled object D such
-- that there is no assembled object A such that D.uid = A.uid? Yes, I think this
-- should be allowed
structure Assembled {lab : Ecosystem.Label} {functionId : lab.MultiMethodId} (argDeconstruction : functionId.ObjectArgNames → DeconstructionKind) where
  withArgumentUid : (arg : functionId.ObjectArgNames) → argDeconstruction arg = .Disassembled → Option SomeObjectData
  withNewUid : List SomeObjectData

structure MultiMethodResult {lab : Ecosystem.Label} (functionId : lab.MultiMethodId) : Type (u + 1) where
  /-- For each object argument we specify its usage. See `Usage`.
  Note that if `argUsage arg = .Destroyed`, then the object that corresponds to `arg` should *not* be put in the destroyed list -/
  argDeconstruction : functionId.ObjectArgNames → DeconstructionKind
  /-- List of assembled objects. Assembled objects will be created.
      It is the responsibility of the user to ensure that
      assembled objects balance with the object arguments that are disassembled -/
  assembled : Assembled argDeconstruction
  /-- List of destroyed objects. Destroyed objects will be balanced with automatically generated ephemeral resources -/
  destroyed : List SomeConsumableObject
  /-- List of constructed objects. Constructed objects will be balanced with automatically generated ephemeral resources -/
  constructed : List SomeObjectData

def MultiMethodResult.numSelvesDestroyed
  {lab : Ecosystem.Label}
  {functionId : lab.MultiMethodId}
  (res : MultiMethodResult functionId)
  : Nat :=
  functionId.objectArgNames.countP (fun a => res.argDeconstruction a == .Destroyed)

structure MultiMethod {lab : Ecosystem.Label} (functionId : lab.MultiMethodId) where
  /-- Computes the result of a function call. See `MultiMethodResult`. -/
  body (selves : functionId.Selves) (args : functionId.Args.type) : Program lab (MultiMethodResult functionId)
  /-- Extra function logic. -/
  invariant (selves : functionId.Selves) (args : functionId.Args.type) : Bool
