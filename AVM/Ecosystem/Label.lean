import AVM.Class.Label
import AVM.Object

namespace AVM.Ecosystem

structure Label : Type 1 where
  name : String

  ClassId : Type
  classLabel : ClassId → Class.Label
  [classesEnum : FinEnum ClassId]
  [classesRepr : Repr ClassId]
  [classesBEq : BEq ClassId]

  -- TODO consider grouping these fields in a struct so that all default values can be provided
  FunctionId : Type := Empty
  FunctionArgs : FunctionId → SomeType := fun _ => ⟨UUnit⟩
  /-- Names of `self` arguments for a given function. -/
  FunctionObjectArgNames : FunctionId → Type := fun _ => UUnit
  /-- Class identifiers for `self` arguments. -/
  FunctionObjectArgClass : {f : FunctionId} → FunctionObjectArgNames f → ClassId
  [objectArgNamesEnum (f : FunctionId) : FinEnum (FunctionObjectArgNames f)]
  [objectArgNamesBEq (f : FunctionId) : BEq (FunctionObjectArgNames f)]
  [functionsFinite : FinEnum FunctionId]
  [functionsRepr : Repr FunctionId]
  [functionsBEq : BEq FunctionId]

def Label.classId (l : Label) (clab : Class.Label) : Option l.ClassId :=
  l.classesEnum.toList.find? (fun b => l.classLabel b == clab)

end AVM.Ecosystem

namespace AVM.Ecosystem.Label

/-- Singleton ecosystem: An ecosystem with a single class, no functions and no intents -/
def singleton (l : Class.Label) : Ecosystem.Label where
  name := l.name

  ClassId := UUnit
  classLabel := fun _ => l

  FunctionObjectArgClass := fun _ => UUnit.unit
  objectArgNamesEnum := fun f => f.elim
  objectArgNamesBEq := fun f => f.elim

def ClassId.label {lab : Ecosystem.Label} (classId : lab.ClassId) : Class.Label :=
  lab.classLabel classId

def ClassId.MemberId {lab : Ecosystem.Label} (c : lab.ClassId) := c.label.MemberId

inductive MemberId (lab : Ecosystem.Label) where
  | functionId (funId : lab.FunctionId)
  | classMember {classId : lab.ClassId} (memId : classId.MemberId)
  /-- Signifies an "always false" member logic. This is used for the member
    logic field of app data, in the created case. It is important that "dummy"
    member logic indicator for the created case always returns false – otherwise
    one could circumvent method logic checks by providing the dummy member logic
    indicator. This could also be represented by an `Option` type in app data,
    but having explicit `falseLogicId` makes its intended behaviour clear. -/
  | falseLogicId

instance ClassId.MemberId.hasTypeRep {lab : Ecosystem.Label} {c : lab.ClassId} : TypeRep c.MemberId := Class.Label.MemberId.hasTypeRep c.label

instance ClassId.MemberId.hasBEq {lab : Ecosystem.Label} {c : lab.ClassId} : BEq c.MemberId := Class.Label.MemberId.hasBEq

instance MemberId.hasBEq {lab : Ecosystem.Label} : BEq (Ecosystem.Label.MemberId lab) where
  beq a b :=
    match a, b with
    | functionId c1, functionId c2 => lab.functionsBEq.beq c1 c2
    | functionId _, _ => false
    | _, functionId _ => false
    | classMember c1, classMember c2 => c1 === c2
    | classMember _, _ => false
    | _, classMember _ => false
    | falseLogicId, falseLogicId => true

def FunctionId.Args {lab : Ecosystem.Label} (functionId : lab.FunctionId) : SomeType :=
  lab.FunctionArgs functionId

def FunctionId.ObjectArgNames {lab : Ecosystem.Label} (functionId : lab.FunctionId) : Type :=
  lab.FunctionObjectArgNames functionId

def FunctionId.objectArgNames {lab : Ecosystem.Label} (functionId : lab.FunctionId) : List functionId.ObjectArgNames :=
  (lab.objectArgNamesEnum functionId).toList

def FunctionId.ObjectArgNames.classId {lab : Ecosystem.Label} {functionId : lab.FunctionId} (argName : functionId.ObjectArgNames) : lab.ClassId :=
  lab.FunctionObjectArgClass argName

/-- Returns the index of an object argument -/
def FunctionId.ObjectArgNames.ix {lab : Ecosystem.Label} {functionId : lab.FunctionId} (argName : functionId.ObjectArgNames) : Fin (lab.objectArgNamesEnum functionId).card :=
  (lab.objectArgNamesEnum functionId).equiv.toFun argName

def FunctionId.numObjectArgs {lab : Ecosystem.Label} {functionId : lab.FunctionId} : Nat :=
  (lab.objectArgNamesEnum functionId).card

def FunctionId.argsClasses {lab : Ecosystem.Label} (functionId : lab.FunctionId) : List lab.ClassId :=
  let getArg (a : functionId.ObjectArgNames) : lab.ClassId := lab.FunctionObjectArgClass a
  List.map getArg functionId.objectArgNames

def MemberId.Args {lab : Ecosystem.Label} (memberId : MemberId lab) : SomeType :=
  match memberId with
  | functionId f => lab.FunctionArgs f
  | classMember m => Class.Label.MemberId.Args m
  | falseLogicId => ⟨UUnit⟩

instance {lab : Ecosystem.Label} {classId : lab.ClassId}
  : CoeHead classId.label.ConstructorId classId.MemberId where
  coe := .constructorId

instance {lab : Ecosystem.Label} {classId : lab.ClassId}
  : CoeHead classId.label.MethodId classId.MemberId where
  coe := .methodId

instance {lab : Ecosystem.Label} {classId : lab.ClassId}
  : CoeHead classId.label.DestructorId classId.MemberId where
  coe := .destructorId

def FunctionId.Selves {lab : Ecosystem.Label} (functionId : lab.FunctionId) : Type :=
  (argName : lab.FunctionObjectArgNames functionId) → Object (lab.FunctionObjectArgClass argName).label

end Ecosystem.Label
