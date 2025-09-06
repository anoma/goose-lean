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

-- Question: Should it be allowed that there exists a disassembled object D such
-- that there is no assembled object A such that D.uid = A.uid? Yes, I think this
-- should be allowed
structure Assembled
  {lab : Ecosystem.Label}
  {multiMethodId : lab.MultiMethodId}
  (argDeconstruction : multiMethodId.ObjectArgNames → DeconstructionKind)
  : Type (u) where
  withArgumentUid : (arg : multiMethodId.ObjectArgNames) → argDeconstruction arg = .Disassembled → Option SomeObjectData.{u}
  withNewUid : List SomeObjectData

structure MultiMethodResult {lab : Ecosystem.Label} (multiMethodId : lab.MultiMethodId) : Type (u) where
  /-- For each object argument we specify its usage. See `Usage`.
  Note that if `argUsage arg = .Destroyed`, then the object that corresponds to `arg` should *not* be put in the destroyed list -/
  argDeconstruction : multiMethodId.ObjectArgNames → DeconstructionKind
  /-- List of assembled objects. Assembled objects will be created.
      It is the responsibility of the user to ensure that
      assembled objects balance with the object arguments that are disassembled -/
  assembled : Assembled.{u} argDeconstruction
  /-- List of destroyed objects. Destroyed objects will be balanced with automatically generated ephemeral resources -/
  destroyed : List SomeConsumableObject
  /-- List of constructed objects. Constructed objects will be balanced with automatically generated ephemeral resources -/
  constructed : List SomeObjectData

def MultiMethodResult.numSelvesDestroyed
  {lab : Ecosystem.Label}
  {multiMethodId : lab.MultiMethodId}
  (res : MultiMethodResult multiMethodId)
  : Nat :=
  multiMethodId.objectArgNames.countP (fun a => res.argDeconstruction a == .Destroyed)

structure MultiMethod.{u} {lab : Ecosystem.Label} (multiMethodId : lab.MultiMethodId) : Type (u + 2) where
  /-- Computes the result of a multiMethod call. See `MultiMethodResult`. -/
  body (selves : multiMethodId.Selves) (args : multiMethodId.Args.type) : Program lab (MultiMethodResult multiMethodId)
  /-- Extra multiMethod logic. -/
  invariant (selves : multiMethodId.Selves) (args : multiMethodId.Args.type) : Bool
