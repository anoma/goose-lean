import Anoma.Resource
import Prelude
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.FinEnum
import AVM.Authorization

abbrev AVM.ObjectId := Anoma.ObjectId

namespace AVM.Class

structure DynamicLabel (PrivateFields : Type) : Type 1 where
  {Label : SomeType.{0}}
  mkDynamicLabel : PrivateFields → Label.type

instance DynamicLabel.instInhabited {A : Type} : Inhabited (DynamicLabel A) where
  default := {Label := ⟨PUnit⟩
              mkDynamicLabel := fun _ => default}

/-- A class label uniquely identifies and specifies a class. The class
  specification provided by a label consists of unique class name, private
  field types, constructor, destructor and method ids. -/
structure Label : Type 1 where
  /-- The name of the class which together with the version uniquely identifies the class.
      Assumption: lab1.name = lab2.name -> lab1.version = lab2.version -> lab1 = lab2. -/
  name : String
  version : Nat := 0
  isUpgradeable : Bool := false

  PrivateFields : SomeType
  [privateFieldsInhabited : Inhabited PrivateFields.type]

  /-- The dynamic label is used to put dynamic data into the Resource label -/
  DynamicLabel : DynamicLabel PrivateFields.type := default

  ConstructorId : Type
  ConstructorArgs : ConstructorId -> SomeType
  ConstructorSignatureId : ConstructorId → Type := fun _ => Empty
  ConstructorSignatureIdEnum : (s : ConstructorId) → FinEnum (ConstructorSignatureId s)
    := by intro s; cases s <;> infer_instance
  [constructorsEnum : FinEnum ConstructorId]
  [constructorsRepr : Repr ConstructorId]
  [constructorsBEq : BEq ConstructorId]
  [constructorsLawfulBEq : LawfulBEq ConstructorId]

  DestructorId : Type := Empty
  DestructorArgs : DestructorId -> SomeType := fun _ => ⟨PUnit⟩
  DestructorSignatureId : DestructorId → Type := fun _ => Empty
  DestructorSignatureIdEnum : (s : DestructorId) → FinEnum (DestructorSignatureId s)
    := by intro s; cases s <;> infer_instance
  [destructorsEnum : FinEnum DestructorId]
  [destructorsRepr : Repr DestructorId]
  [destructorsBEq : BEq DestructorId]
  [destructorsLawfulBEq : LawfulBEq DestructorId]

  MethodId : Type
  MethodArgs : MethodId -> SomeType
  MethodSignatureId : MethodId → Type := fun _ => Empty
  MethodSignatureIdEnum : (s : MethodId) → FinEnum (MethodSignatureId s)
    := by intro s; cases s <;> infer_instance
  [methodsEnum : FinEnum MethodId]
  [methodsRepr : Repr MethodId]
  [methodsBEq : BEq MethodId]
  [methodsLawfulBEq : LawfulBEq MethodId]

instance Label.instHashable : Hashable Label where
  hash l := hash l.name

def Label.dummy : Label where
  name := "Dummy"
  PrivateFields := ⟨PUnit⟩
  DynamicLabel := default
  ConstructorId := PUnit
  ConstructorArgs := fun _ => ⟨PUnit⟩
  constructorsEnum := inferInstanceAs (FinEnum PUnit)
  constructorsRepr := inferInstanceAs (Repr PUnit)
  constructorsBEq := inferInstanceAs (BEq PUnit)
  DestructorId := Empty
  MethodId := Empty
  MethodArgs f := nomatch f

def Label.logicRef (lab : Label) : Anoma.LogicRef :=
  ⟨"class-logic-" ++ lab.name⟩

inductive Label.MemberId (lab : Class.Label) : Type where
  | constructorId (constrId : lab.ConstructorId) : MemberId lab
  | destructorId (destructorId : lab.DestructorId) : MemberId lab
  | methodId (methodId : lab.MethodId) : MemberId lab
  | upgradeId : MemberId lab

abbrev Label.MemberId.SignatureId {lab : Class.Label} : Label.MemberId lab → Type
  | .methodId m => lab.MethodSignatureId m
  | .destructorId m => lab.DestructorSignatureId m
  | .constructorId m => lab.ConstructorSignatureId m
  | .upgradeId => Empty

instance Label.MemberId.instHashable {lab : Class.Label} : Hashable (Class.Label.MemberId lab) where
  hash l := Hashable.Mix.run do
    mix lab
    match l with
    | .upgradeId =>
      mix 0
    | .methodId m =>
      mix 1
      mix (lab.methodsEnum.equiv m)
    | .destructorId m =>
      mix 2
      mix (lab.destructorsEnum.equiv m)
    | .constructorId m =>
      mix 3
      mix (lab.constructorsEnum.equiv m)

instance Label.MemberId.hasBEq {lab : Class.Label} : BEq (Class.Label.MemberId lab) where
  beq a b :=
    match a, b with
    | constructorId c1, constructorId c2 => lab.constructorsBEq.beq c1 c2
    | constructorId _, _ => false
    | _, constructorId _ => false
    | destructorId c1, destructorId c2 => lab.destructorsBEq.beq c1 c2
    | destructorId _, _ => false
    | _, destructorId _ => false
    | methodId m1, methodId m2 => lab.methodsBEq.beq m1 m2
    | methodId _, _ => false
    | _, methodId _ => false
    | upgradeId, upgradeId => true

instance Label.MemberId.instReflBEq {lab : Class.Label} : ReflBEq lab.MemberId where
  rfl := by
    intro a
    have := lab.constructorsLawfulBEq
    have := lab.destructorsLawfulBEq
    have := lab.methodsLawfulBEq
    cases a
    iterate 4 {
      unfold BEq.beq Label.MemberId.hasBEq
      simp
    }

instance Label.MemberId.instLawfulBEq {lab : Class.Label} : LawfulBEq (Class.Label.MemberId lab) where
  eq_of_beq := by
    intro a b
    have := lab.constructorsLawfulBEq
    have := lab.destructorsLawfulBEq
    have := lab.methodsLawfulBEq
    unfold BEq.beq Label.MemberId.hasBEq
    cases a <;> cases b <;> simp

instance Label.MemberId.hasTypeRep (lab : Class.Label) : TypeRep (Class.Label.MemberId lab) where
  rep := Rep.composite "AVM.Class.Label.MemberId" [Rep.atomic lab.name]

abbrev Label.ConstructorId.Args {lab : Class.Label} (constrId : lab.ConstructorId) : SomeType :=
  lab.ConstructorArgs constrId

abbrev Label.MethodId.Args {lab : Class.Label} (methodId : lab.MethodId) : SomeType :=
  lab.MethodArgs methodId

abbrev Label.DestructorId.Args {lab : Class.Label} (destructorId : lab.DestructorId) : SomeType.{0} :=
  lab.DestructorArgs destructorId

def Label.MemberId.Args {lab : Class.Label} (memberId : MemberId lab) : SomeType :=
  match memberId with
  | constructorId c => lab.ConstructorArgs c
  | destructorId c => lab.DestructorArgs c
  | methodId c => lab.MethodArgs c
  | upgradeId => ⟨PUnit⟩

abbrev Label.MemberId.Signatures
  {lab : Class.Label}
  (f : MemberId lab)
  (args : f.Args.type)
  : Type :=
  f.SignatureId → Signature (f, args)

abbrev Label.MethodId.Signatures
  {lab : Class.Label}
  (f : lab.MethodId)
  (args : f.Args.type)
  : Type :=
  MemberId.methodId f |>.Signatures args

abbrev Label.ConstructorId.Signatures
  {lab : Class.Label}
  (f : lab.ConstructorId)
  (args : f.Args.type)
  : Type :=
  MemberId.constructorId f |>.Signatures args

abbrev Label.DestructorId.Signatures
  {lab : Class.Label}
  (f : lab.DestructorId)
  (args : f.Args.type)
  : Type :=
  MemberId.destructorId f |>.Signatures args

instance Label.hasTypeRep : TypeRep Label where
  rep := Rep.atomic "AVM.Class.Label"

instance Label.hasBEq : BEq Label where
  beq a b :=
    a.name == b.name
      && a.version == b.version
      && a.PrivateFields == b.PrivateFields
