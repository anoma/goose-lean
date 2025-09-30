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
  [isObject : IsObject type]
--  withLabel : isObject.label = (label.MultiMethodObjectArgClass argName).label := by rfl

def ObjectArgs
  (lab : AVM.Ecosystem.Label)
  (multiId : lab.MultiMethodId)
  (argsInfo : (a : multiId.ObjectArgNames) → ObjectArgInfo lab multiId a)
  : Type
  := (a : multiId.ObjectArgNames) → (argsInfo a).type

structure DestroyableObject where
  object : AnObject
  key : Anoma.NullifierKey := Anoma.NullifierKey.universal

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

structure MultiMethodResult {lab : AVM.Ecosystem.Label} (multiId : lab.MultiMethodId) where
  argDeconstruction : multiId.ObjectArgNames → AVM.DeconstructionKind := fun _ => .Disassembled
  assembled : Assembled argDeconstruction := default
  constructed : List AnObject := []

def MultiMethodResult.empty {lab : AVM.Ecosystem.Label} (multiId : lab.MultiMethodId) : MultiMethodResult multiId :=
  {assembled := default, constructed := []}

def MultiMethodResult.toAVM {lab : AVM.Ecosystem.Label} {multiId : lab.MultiMethodId} (r : MultiMethodResult multiId) : AVM.MultiMethodResult multiId where
  argDeconstruction := r.argDeconstruction
  assembled := r.assembled.toAVM
  constructed := r.constructed.map (·.toSomeObjectData)

def defFunction
  (lab : Ecosystem.Label)
  (funId : lab.FunctionId)
  (argsInfo : (a : funId.ObjectArgNames) → ObjectArgInfo lab funId a)
  (body : ObjectArgs lab funId argsInfo → funId.Args.type → FunctionResult funId)
  (invariant : ObjectArgs lab funId argsInfo → funId.Args.type → Bool := fun _ _ => true)
  : Function funId where
  body (selves : funId.Selves) (args : funId.Args.type) : AVM.FunctionResult funId :=
    match FinEnum.decImageOption' (enum := lab.objectArgNamesEnum funId) (getArg selves) with
    | none => FunctionResult.empty funId |>.toAVM
    | some (p : (argName : funId.ObjectArgNames) → (argsInfo argName).type) => (body p args).toAVM
  invariant (selves : funId.Selves) (args : funId.Args.type) : Bool :=
    match FinEnum.decImageOption' (enum := lab.objectArgNamesEnum funId) (getArg selves) with
    | none => false
    | some (p : (argName : funId.ObjectArgNames) → (argsInfo argName).type) => invariant p args
  where
  getArg (selves : funId.Selves) (argName : funId.ObjectArgNames) : Option (argsInfo argName).type :=
    (argsInfo argName).isObject.fromObject
    (by rw [(argsInfo argName).withLabel]
        exact selves argName)
