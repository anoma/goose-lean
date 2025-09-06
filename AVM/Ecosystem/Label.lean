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

  MultiMethodId : Type := Empty
  /-- Type of multiMethod arguments excluding `self` arguments. -/
  MultiMethodArgs : MultiMethodId → SomeType := fun _ => ⟨PUnit⟩
  /-- Names of `self` arguments for a given multiMethod. -/
  MultiMethodObjectArgNames : MultiMethodId → Type := fun _ => PUnit
  /-- Class identifiers for `self` arguments. -/
  MultiMethodObjectArgClass : {f : MultiMethodId} → MultiMethodObjectArgNames f → ClassId
  [objectArgNamesEnum (f : MultiMethodId) : FinEnum (MultiMethodObjectArgNames f)]
  [objectArgNamesBEq (f : MultiMethodId) : BEq (MultiMethodObjectArgNames f)]
  [multiMethodsFinite : FinEnum MultiMethodId]
  [multiMethodsRepr : Repr MultiMethodId]
  [multiMethodsBEq : BEq MultiMethodId]

def Label.classId (l : Label) (clab : Class.Label) : Option l.ClassId :=
  l.classesEnum.toList.find? (fun b => l.classLabel b == clab)

instance hasBEq : BEq Label where
  beq a b := a.name == b.name

end AVM.Ecosystem

namespace AVM.Ecosystem.Label


/-- Singleton ecosystem: An ecosystem with a single class, no multiMethods and no intents -/
def singleton (l : Class.Label) : Ecosystem.Label where
  name := l.name

  ClassId := PUnit
  classLabel := fun _ => l

  MultiMethodObjectArgClass {f : Empty} := f.elim

def dummy : Label := singleton Class.Label.dummy

def MultiMethodObjectArgNames.classId
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (arg : lab.MultiMethodObjectArgNames multiId)
  : lab.ClassId := lab.MultiMethodObjectArgClass arg

namespace ClassId

def label {lab : Ecosystem.Label} (classId : lab.ClassId) : Class.Label.{0} :=
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

namespace MultiMethodId

def Args {lab : Ecosystem.Label} (multiMethodId : lab.MultiMethodId) : SomeType :=
  lab.MultiMethodArgs multiMethodId

def ObjectArgNames {lab : Ecosystem.Label} (multiMethodId : lab.MultiMethodId) : Type :=
  lab.MultiMethodObjectArgNames multiMethodId

def numObjectArgs {lab : Ecosystem.Label} {multiMethodId : lab.MultiMethodId} : Nat :=
  (lab.objectArgNamesEnum multiMethodId).card

def objectArgNames {lab : Ecosystem.Label} (multiMethodId : lab.MultiMethodId) : List multiMethodId.ObjectArgNames :=
  (lab.objectArgNamesEnum multiMethodId).toList

def objectArgNamesVec {lab : Ecosystem.Label} (multiMethodId : lab.MultiMethodId) : Vector multiMethodId.ObjectArgNames multiMethodId.numObjectArgs :=
  (lab.objectArgNamesEnum multiMethodId).toVector

def ObjectArgNames.classId {lab : Ecosystem.Label} {multiMethodId : lab.MultiMethodId} (argName : multiMethodId.ObjectArgNames) : lab.ClassId :=
  lab.MultiMethodObjectArgClass argName

/-- Returns the index of an object argument -/
def ObjectArgNames.ix {lab : Ecosystem.Label} {multiMethodId : lab.MultiMethodId} (argName : multiMethodId.ObjectArgNames) : Fin (lab.objectArgNamesEnum multiMethodId).card :=
  (lab.objectArgNamesEnum multiMethodId).equiv.toFun argName

def argsClasses {lab : Ecosystem.Label} (multiMethodId : lab.MultiMethodId) : List lab.ClassId :=
  let getArg (a : multiMethodId.ObjectArgNames) : lab.ClassId := lab.MultiMethodObjectArgClass a
  List.map getArg multiMethodId.objectArgNames

def Selves {lab : Ecosystem.Label} (multiMethodId : lab.MultiMethodId) : Type :=
  (argName : lab.MultiMethodObjectArgNames multiMethodId) → Object (lab.MultiMethodObjectArgClass argName).label

def SelvesFromHList
  {lab : Ecosystem.Label}
  (multiId : lab.MultiMethodId)
  (l : HList (multiId.argsClasses.map (fun c => Object c.label)))
  : multiId.Selves := sorry

def SelvesIds
  {lab : Ecosystem.Label}
  (multiMethodId : lab.MultiMethodId)
  : Type :=
  (argName : lab.MultiMethodObjectArgNames multiMethodId) → ObjectId

end MultiMethodId

inductive MemberId (lab : Ecosystem.Label) where
  | multiMethodId (funId : lab.MultiMethodId)
  | classMember {classId : lab.ClassId} (memId : classId.MemberId)

namespace MemberId

def Args {lab : Ecosystem.Label} (memberId : MemberId lab) : SomeType :=
  match memberId with
  | multiMethodId f => lab.MultiMethodArgs f
  | classMember m => Class.Label.MemberId.Args m

instance hasBEq {lab : Ecosystem.Label} : BEq (Ecosystem.Label.MemberId lab) where
  beq a b :=
    match a, b with
    | multiMethodId c1, multiMethodId c2 => lab.multiMethodsBEq.beq c1 c2
    | multiMethodId _, _ => false
    | _, multiMethodId _ => false
    | classMember c1, classMember c2 => c1 === c2

def numObjectArgs {lab : Ecosystem.Label} (memberId : MemberId lab) : Nat :=
  match memberId with
  | multiMethodId f => f.numObjectArgs
  | classMember _ => 1

end MemberId
