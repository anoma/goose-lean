import AVM.Class.Label
import AVM.Authorization

namespace AVM.Ecosystem

structure Label : Type 1 where
  name : String

  ClassId : Type
  classLabel : ClassId → Class.Label
  [classesEnum : FinEnum ClassId]
  [classesRepr : Repr ClassId]
  [classesBEq : BEq ClassId]
  [classesDecidableEq : DecidableEq ClassId]

  MultiMethodId : Type := Empty
  /-- Type of multiMethod arguments excluding `self` arguments. -/
  MultiMethodArgs : MultiMethodId → SomeType := fun _ => ⟨PUnit⟩
  /-- Names of `self` arguments for a given multiMethod. -/
  MultiMethodObjectArgNames : MultiMethodId → Type := fun _ => PUnit
  /-- Class identifiers for `self` arguments. -/
  MultiMethodObjectArgClass : {f : MultiMethodId} → MultiMethodObjectArgNames f → ClassId
  [ObjectArgNamesEnum (f : MultiMethodId) : FinEnum (MultiMethodObjectArgNames f)]
  [ObjectArgNamesBEq (f : MultiMethodId) : BEq (MultiMethodObjectArgNames f)]
  [multiMethodsFinite : FinEnum MultiMethodId]
  [multiMethodsRepr : Repr MultiMethodId]
  [multiMethodsBEq : BEq MultiMethodId]
  [multiMethodsLawfulBEq : LawfulBEq MultiMethodId]

instance Label.hasTypeRep : TypeRep Label where
  rep := Rep.atomic "AVM.Ecosystem.Label"

def Label.classId (l : Label) (clab : Class.Label) : Option l.ClassId :=
  l.classesEnum.toList.find? (fun b => l.classLabel b == clab)

instance hasBEq : BEq Label where
  beq a b := a.name == b.name

end AVM.Ecosystem

def Fin.classId
  {lab : AVM.Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (arg : Fin (lab.ObjectArgNamesEnum multiId).card)
  : lab.ClassId := lab.MultiMethodObjectArgClass ((lab.ObjectArgNamesEnum multiId).equiv.invFun arg)

namespace AVM.Ecosystem.Label

def logicRef (lab : Label) : Anoma.LogicRef :=
  ⟨"logic-of-ecosystem-" ++ lab.name⟩

/-- Singleton ecosystem: An ecosystem with a single class, no multiMethods and no intents -/
def singleton (l : Class.Label) : Ecosystem.Label where
  name := l.name

  ClassId := PUnit
  classLabel := fun _ => l

  MultiMethodObjectArgClass {f : Empty} := f.elim

def dummy : Label := singleton Class.Label.dummy

def instInhabited : Inhabited Ecosystem.Label where
  default := dummy

def MultiMethodObjectArgNames.classId
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (arg : lab.MultiMethodObjectArgNames multiId)
  : lab.ClassId := lab.MultiMethodObjectArgClass arg

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

namespace MultiMethodId

def Args {lab : Ecosystem.Label} (multiId : lab.MultiMethodId) : SomeType :=
  lab.MultiMethodArgs multiId

def Signatures {lab : Ecosystem.Label} (multiId : lab.MultiMethodId) (_args : multiId.Args.type) : Type :=
  Unit

def ObjectArgNames {lab : Ecosystem.Label} (multiId : lab.MultiMethodId) : Type :=
  lab.MultiMethodObjectArgNames multiId

def ObjectArgNamesEnum {lab : Ecosystem.Label} (multiId : lab.MultiMethodId) : FinEnum (lab.MultiMethodObjectArgNames multiId) := lab.ObjectArgNamesEnum multiId

def numObjectArgs {lab : Ecosystem.Label} {multiId : lab.MultiMethodId} : Nat :=
  (lab.ObjectArgNamesEnum multiId).card

def objectArgNamesVec {lab : Ecosystem.Label} (multiId : lab.MultiMethodId) : List.Vector multiId.ObjectArgNames multiId.numObjectArgs :=
  (lab.ObjectArgNamesEnum multiId).toVector

def ObjectArgNames.classId {lab : Ecosystem.Label} {multiId : lab.MultiMethodId} (argName : multiId.ObjectArgNames) : lab.ClassId :=
  lab.MultiMethodObjectArgClass argName

/-- Returns the index of an object argument -/
def ObjectArgNames.ix {lab : Ecosystem.Label} {multiId : lab.MultiMethodId} (argName : multiId.ObjectArgNames) : Fin (lab.ObjectArgNamesEnum multiId).card :=
  (lab.ObjectArgNamesEnum multiId).equiv.toFun argName

def argsClassesVec {lab : Ecosystem.Label} (multiId : lab.MultiMethodId) : List.Vector lab.ClassId multiId.numObjectArgs :=
  List.Vector.ofFn (fun (a : Fin numObjectArgs) => lab.MultiMethodObjectArgClass
  ((lab.ObjectArgNamesEnum multiId).equiv.invFun a))

end MultiMethodId

inductive MemberId (lab : Ecosystem.Label) : Type where
  | multiMethodId (funId : lab.MultiMethodId)
  | classMember {classId : lab.ClassId} (memId : classId.MemberId)

namespace MemberId

instance instBEq {lab : Ecosystem.Label} : BEq (MemberId lab) where
  beq a b :=
  have := lab.classesDecidableEq
  match a, b with
  | .multiMethodId m1, .multiMethodId m2 =>
    have := lab.multiMethodsBEq
    m1 == m2
  | .multiMethodId _ , _ => false
  | _, .multiMethodId _ => false
  | .classMember (classId := c1) m1, classMember (classId := c2) m2 =>
    if h : c1 = c2
    then m1 == h ▸ m2
    else false

instance instReflBEq {lab : Ecosystem.Label} : ReflBEq (MemberId lab) where
  rfl := by
    have := lab.multiMethodsLawfulBEq
    intro a; cases a
    unfold BEq.beq instBEq; simp
    case classMember classId classMem =>
    unfold BEq.beq instBEq;
    have i : ReflBEq classId.MemberId := @Class.Label.MemberId.instReflBEq classId.label
    simp

-- TODO simplify
instance instLawfulBEq {lab : Ecosystem.Label} : LawfulBEq lab.MemberId where
  eq_of_beq := by
    intro a b e
    have i := lab.multiMethodsLawfulBEq
    unfold BEq.beq instBEq at e; simp at e; split at e; simp
    apply i.eq_of_beq
    assumption
    contradiction
    contradiction
    split at e
    case h_4.isTrue _ _ _ _ h =>
      subst h;
      have x := Class.Label.MemberId.instLawfulBEq.eq_of_beq e
      subst x; simp
    contradiction

abbrev SignatureId (lab : Ecosystem.Label) : MemberId lab → Type
  | .classMember m => m.SignatureId
  | _ => Empty

abbrev Args {lab : Ecosystem.Label} (memberId : MemberId lab) : SomeType.{0} :=
  match memberId with
  | multiMethodId f => lab.MultiMethodArgs f
  | classMember m => Class.Label.MemberId.Args m

abbrev Signatures {lab : Ecosystem.Label} (mem : MemberId lab) (args : mem.Args.type)
  : Type :=
  match mem with
  | .classMember m => m.Signatures args
  | .multiMethodId m => m.Signatures args

def numObjectArgs {lab : Ecosystem.Label} (memberId : MemberId lab) : Nat :=
  match memberId with
  | multiMethodId f => f.numObjectArgs
  | classMember _ => 1

end MemberId
