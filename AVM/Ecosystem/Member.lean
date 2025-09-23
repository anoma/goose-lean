import AVM.Program
import AVM.Ecosystem.Label
import AVM.Ecosystem.Data
import AVM.Object.Consumed

namespace AVM

inductive DeconstructionKind : Type where
  /-- Will be consumed and automatically balanced with an ephemeral resource -/
  | Destroyed
  /-- Will be consumed. It is the responsibility of the user to balance disassembled objects with assembled objects -/
  | Disassembled
  deriving BEq, DecidableEq, Inhabited

structure Assembled
  {label : Ecosystem.Label}
  {multiId : label.MultiMethodId}
  (argDeconstruction : multiId.ObjectArgNames → DeconstructionKind)
  : Type 1 where
  /-- It is possible that a disassembled Object's uid is not in any of the created objects. Consider
      the situation when you want to split an object into two and it is desirable that none of the
      spawned objects has the uid of the original --/
  withOldUid : (arg : multiId.ObjectArgNames) → argDeconstruction arg = .Disassembled → Option (ObjectData arg.classId)
  withNewUid : List SomeObjectData
  deriving Inhabited

structure AssembledOldUid
  {label : Ecosystem.Label}
  {multiId : label.MultiMethodId}
  {argDeconstruction : multiId.ObjectArgNames → DeconstructionKind}
  (a : Assembled argDeconstruction)
  : Type 1 where
  arg : multiId.ObjectArgNames
  objectData : ObjectData arg.classId
  disassembled : argDeconstruction arg = .Disassembled
  correct : a.withOldUid arg disassembled = some objectData

def Assembled.withOldUidList
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  {argDeconstruction : multiId.ObjectArgNames → DeconstructionKind}
  (assembled : Assembled argDeconstruction)
  : List (AssembledOldUid assembled)
  := multiId.objectArgNamesVec.toList.filterMap fun arg =>
    if disassembled : argDeconstruction arg = .Disassembled
    then match correct : assembled.withOldUid arg disassembled with
         | none => none
         | some objectData => some
            { arg
              objectData
              disassembled
              correct }
    else none

instance Assembled.instInhabited
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (argDeconstruction : multiId.ObjectArgNames → DeconstructionKind)
  : Inhabited (Assembled argDeconstruction) where
  default :=
    { withNewUid := []
      withOldUid := fun _ _ => .none }

structure MultiMethodResult {lab : Ecosystem.Label} (multiId : lab.MultiMethodId) : Type 1 where
  /-- For each object argument we specify its `DeconstructionKind`. -/
  argDeconstruction : multiId.ObjectArgNames → DeconstructionKind
  /-- List of assembled objects. Assembled objects will be created.
      It is the responsibility of the user to ensure that
      assembled objects balance with the object arguments that are disassembled -/
  assembled : Assembled argDeconstruction
  /-- List of constructed objects. Constructed objects will be balanced with automatically generated ephemeral resources -/
  constructed : List ObjectValue := []
  deriving Inhabited

namespace MultiMethodResult

instance instInhabited {lab : Ecosystem.Label} {multiId : lab.MultiMethodId} : Inhabited (MultiMethodResult multiId) where
  default :=
    { argDeconstruction := fun _ => .Disassembled
      assembled := default
      constructed := [] }

def data
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (res : MultiMethodResult multiId)
  : MultiMethodData :=
  { numConstructed := res.constructed.length
    numSelvesDestroyed := multiId.objectArgNamesVec.toList.countP (fun x => res.argDeconstruction x == .Destroyed)
    numReassembledNewUid := res.assembled.withNewUid.length
    numReassembledOldUid := res.assembled.withOldUidList.length }

end MultiMethodResult

structure Ecosystem.MultiMethod {lab : Ecosystem.Label} (multiId : lab.MultiMethodId) : Type 1 where
  /-- Computes the result of a multiMethod call. See `MultiMethodResult`. -/
  body (selves : multiId.Selves) (args : multiId.Args.type) : Program.{1} lab (MultiMethodResult multiId)
  /-- Extra multiMethod logic. -/
  invariant (selves : multiId.Selves) (args : multiId.Args.type) : Bool
