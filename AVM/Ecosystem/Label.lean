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

  FunctionId : Type := Empty
  /-- Type of function arguments excluding `self` arguments. -/
  FunctionArgs : FunctionId → SomeType := fun _ => ⟨PUnit⟩
  /-- Names of `self` arguments for a given function. -/
  FunctionObjectArgNames : FunctionId → Type := fun _ => PUnit
  /-- Class identifiers for `self` arguments. -/
  FunctionObjectArgClass : {f : FunctionId} → FunctionObjectArgNames f → ClassId
  [objectArgNamesEnum (f : FunctionId) : FinEnum (FunctionObjectArgNames f)]
  [objectArgNamesBEq (f : FunctionId) : BEq (FunctionObjectArgNames f)]
  [functionsFinite : FinEnum FunctionId]
  [functionsRepr : Repr FunctionId]
  [functionsBEq : BEq FunctionId]

def Label.classId (l : Label) (clab : Class.Label) : Option l.ClassId :=
  l.classesEnum.toList.find? (fun b => l.classLabel b == clab)

instance hasBEq : BEq Label where
  beq a b := a.name == b.name

end AVM.Ecosystem

namespace AVM.Ecosystem.Label

/-- Singleton ecosystem: An ecosystem with a single class, no functions and no intents -/
def singleton (l : Class.Label) : Ecosystem.Label where
  name := l.name

  ClassId := PUnit
  classLabel := fun _ => l

  FunctionObjectArgClass {f : Empty} := f.elim

def dummy : Label := singleton Class.Label.dummy

namespace ClassId

def label {lab : Ecosystem.Label} (classId : lab.ClassId) : Class.Label :=
  lab.classLabel classId

def MemberId {lab : Ecosystem.Label} (c : lab.ClassId) := c.label.MemberId

instance MemberId.hasTypeRep {lab : Ecosystem.Label} {c : lab.ClassId} : TypeRep c.MemberId := Class.Label.MemberId.hasTypeRep c.label

instance MemberId.hasBEq {lab : Ecosystem.Label} {c : lab.ClassId} : BEq c.MemberId := Class.Label.MemberId.hasBEq

end ClassId

instance {lab : Ecosystem.Label} {classId : lab.ClassId}
  : CoeHead classId.label.ConstructorId classId.MemberId where
  coe := .constructorId

instance {lab : Ecosystem.Label} {classId : lab.ClassId}
  : CoeHead classId.label.MethodId classId.MemberId where
  coe := .methodId

instance {lab : Ecosystem.Label} {classId : lab.ClassId}
  : CoeHead classId.label.DestructorId classId.MemberId where
  coe := .destructorId

namespace FunctionId

def Args {lab : Ecosystem.Label} (functionId : lab.FunctionId) : SomeType :=
  lab.FunctionArgs functionId

def ObjectArgNames {lab : Ecosystem.Label} (functionId : lab.FunctionId) : Type :=
  lab.FunctionObjectArgNames functionId

def objectArgNames {lab : Ecosystem.Label} (functionId : lab.FunctionId) : List functionId.ObjectArgNames :=
  (lab.objectArgNamesEnum functionId).toList

def ObjectArgNames.classId {lab : Ecosystem.Label} {functionId : lab.FunctionId} (argName : functionId.ObjectArgNames) : lab.ClassId :=
  lab.FunctionObjectArgClass argName

/-- Returns the index of an object argument -/
def ObjectArgNames.ix {lab : Ecosystem.Label} {functionId : lab.FunctionId} (argName : functionId.ObjectArgNames) : Fin (lab.objectArgNamesEnum functionId).card :=
  (lab.objectArgNamesEnum functionId).equiv.toFun argName

def numObjectArgs {lab : Ecosystem.Label} {functionId : lab.FunctionId} : Nat :=
  (lab.objectArgNamesEnum functionId).card

def argsClasses {lab : Ecosystem.Label} (functionId : lab.FunctionId) : List lab.ClassId :=
  let getArg (a : functionId.ObjectArgNames) : lab.ClassId := lab.FunctionObjectArgClass a
  List.map getArg functionId.objectArgNames

def Selves {lab : Ecosystem.Label} (functionId : lab.FunctionId) : Type :=
  (argName : lab.FunctionObjectArgNames functionId) → Object (lab.FunctionObjectArgClass argName).label

end FunctionId

inductive MemberId (lab : Ecosystem.Label) where
  | functionId (funId : lab.FunctionId)
  | classMember {classId : lab.ClassId} (memId : classId.MemberId)

namespace MemberId

def Args {lab : Ecosystem.Label} (memberId : MemberId lab) : SomeType :=
  match memberId with
  | functionId f => lab.FunctionArgs f
  | classMember m => Class.Label.MemberId.Args m

instance hasBEq {lab : Ecosystem.Label} : BEq (Ecosystem.Label.MemberId lab) where
  beq a b :=
    match a, b with
    | functionId c1, functionId c2 => lab.functionsBEq.beq c1 c2
    | functionId _, _ => false
    | _, functionId _ => false
    | classMember c1, classMember c2 => c1 === c2

def numObjectArgs {lab : Ecosystem.Label} (memberId : MemberId lab) : Nat :=
  match memberId with
  | functionId f => f.numObjectArgs
  | classMember _ => 1

end MemberId
