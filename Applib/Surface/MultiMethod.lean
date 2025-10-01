import AVM
import Applib.Surface.Member
import Applib.Surface.Program

namespace Applib

structure ObjectArgInfo
  (label : AVM.Ecosystem.Label)
  (multiId : label.MultiMethodId)
  (argName : label.MultiMethodObjectArgNames multiId)
  : Type 1 where
  type : Type
  [isObjectOf : IsObjectOf (label.MultiMethodObjectArgClass argName) type]

def ObjectArgs
  (lab : AVM.Ecosystem.Label)
  (multiId : lab.MultiMethodId)
  (argsInfo : (a : multiId.ObjectArgNames) → ObjectArgInfo lab multiId a)
  : Type
  := (a : multiId.ObjectArgNames) → (argsInfo a).type

structure Assembled
  {label : AVM.Ecosystem.Label}
  {multiId : label.MultiMethodId}
  (argDeconstruction : multiId.ObjectArgNames → AVM.DeconstructionKind)
  : Type 1 where
  /-- It is possible that a disassembled Object's uid is not in any of the created objects. Consider
      the situation when you want to split an object into two and it is desirable that none of the
      spawned objects has the uid of the original --/
  withOldUid : (arg : multiId.ObjectArgNames) → argDeconstruction arg = .Disassembled → Option (AnObjectOf arg.classId)
  withNewUid : List AnObject
  deriving Inhabited

def Assembled.toAVM
  {lab : AVM.Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  {argDeconstruction : multiId.ObjectArgNames → AVM.DeconstructionKind}
  (a : Assembled argDeconstruction)
  : AVM.Assembled argDeconstruction
  := { withOldUid := fun arg disassembled =>
        (a.withOldUid arg disassembled).map (·.toObjectData),
       withNewUid := a.withNewUid.map (·.toSomeObjectData) }

structure MultiMethodResult {lab : AVM.Ecosystem.Label} (multiId : lab.MultiMethodId) : Type 1 where
  argDeconstruction : multiId.ObjectArgNames → AVM.DeconstructionKind := fun _ => .Disassembled
  assembled : Assembled argDeconstruction := default
  constructed : List AnObject := []

def MultiMethodResult.empty {lab : AVM.Ecosystem.Label} (multiId : lab.MultiMethodId) : MultiMethodResult multiId :=
  {assembled := default, constructed := []}

def MultiMethodResult.toAVM {lab : AVM.Ecosystem.Label} {multiId : lab.MultiMethodId} (r : MultiMethodResult multiId) : AVM.MultiMethodResult multiId where
  argDeconstruction := r.argDeconstruction
  assembled := r.assembled.toAVM
  constructed := r.constructed.map (·.toSomeObjectData)

def defMultiMethod
  (lab : AVM.Ecosystem.Label)
  (multiId : lab.MultiMethodId)
  (argsInfo : (a : multiId.ObjectArgNames) → ObjectArgInfo lab multiId a)
  (body : ObjectArgs lab multiId argsInfo → multiId.Args.type → Program lab (MultiMethodResult multiId))
  (invariant : ObjectArgs lab multiId argsInfo → (args : multiId.Args.type) → (signatures : multiId.Signatures args) → Bool := fun _ _ _ => true)
  : AVM.Ecosystem.MultiMethod multiId where
  body (selves : multiId.Selves) (args : multiId.Args.type) : AVM.Program lab (AVM.MultiMethodResult multiId) :=
    (body (getArg selves) args).map (MultiMethodResult.toAVM) |>.toAVM
  invariant (selves : multiId.Selves) (args : multiId.Args.type) (signatures : multiId.Signatures args) : Bool :=
    invariant (getArg selves) args signatures
  where
    getArg (selves : multiId.Selves) (argName : multiId.ObjectArgNames) : (argsInfo argName).type :=
      (argsInfo argName).isObjectOf.fromObject (selves argName).data
