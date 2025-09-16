import Anoma.Resource
import Prelude
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.FinEnum

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

  PrivateFields : SomeType
  [privateFieldsInhabited : Inhabited PrivateFields.type]

  /-- The dynamic label is used to put dynamic data into the Resource label -/
  DynamicLabel : DynamicLabel PrivateFields.type := default

  ConstructorId : Type
  ConstructorArgs : ConstructorId -> SomeType
  [constructorsFinite : Fintype ConstructorId]
  [constructorsRepr : Repr ConstructorId]
  [constructorsBEq : BEq ConstructorId]

  DestructorId : Type := Empty
  DestructorArgs : DestructorId -> SomeType := fun _ => ⟨PUnit⟩
  [destructorsFinite : Fintype DestructorId]
  [destructorsRepr : Repr DestructorId]
  [destructorsBEq : BEq DestructorId]

  MethodId : Type
  MethodArgs : MethodId -> SomeType
  [methodsFinite : Fintype MethodId]
  [methodsRepr : Repr MethodId]
  [methodsBEq : BEq MethodId]

def Label.dummy : Label where
  name := "Dummy"
  PrivateFields := ⟨PUnit⟩
  DynamicLabel := default
  ConstructorId := PUnit
  ConstructorArgs := fun _ => ⟨PUnit⟩
  constructorsFinite := inferInstanceAs (Fintype PUnit)
  constructorsRepr := inferInstanceAs (Repr PUnit)
  constructorsBEq := inferInstanceAs (BEq PUnit)
  DestructorId := Empty
  DestructorArgs := fun _ => ⟨PUnit⟩
  destructorsFinite := inferInstanceAs (Fintype Empty)
  destructorsRepr := inferInstanceAs (Repr Empty)
  destructorsBEq := inferInstanceAs (BEq Empty)
  MethodId := PUnit
  MethodArgs := fun _ => ⟨PUnit⟩
  methodsFinite := inferInstanceAs (Fintype PUnit)
  methodsRepr := inferInstanceAs (Repr PUnit)
  methodsBEq := inferInstanceAs (BEq PUnit)

inductive Label.MemberId (lab : Class.Label) where
  | constructorId (constrId : lab.ConstructorId) : MemberId lab
  | destructorId (destructorId : lab.DestructorId) : MemberId lab
  | methodId (methodId : lab.MethodId) : MemberId lab

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

instance Label.MemberId.hasTypeRep (lab : Class.Label) : TypeRep (Class.Label.MemberId lab) where
  rep := Rep.composite "AVM.Class.Label.MemberId" [Rep.atomic lab.name]

def Label.ConstructorId.Args {lab : Class.Label} (constrId : lab.ConstructorId) : SomeType :=
  lab.ConstructorArgs constrId

def Label.MethodId.Args {lab : Class.Label} (methodId : lab.MethodId) : SomeType :=
  lab.MethodArgs methodId

def Label.DestructorId.Args {lab : Class.Label} (destructorId : lab.DestructorId) : SomeType.{0} :=
  lab.DestructorArgs destructorId

def Label.MemberId.Args {lab : Class.Label} (memberId : MemberId lab) : SomeType :=
  match memberId with
  | constructorId c => lab.ConstructorArgs c
  | destructorId c => lab.DestructorArgs c
  | methodId c => lab.MethodArgs c

instance Label.hasTypeRep : TypeRep Label where
  rep := Rep.atomic "AVM.Class.Label"

instance Label.hasBEq : BEq Label where
  beq a b :=
    a.name == b.name
      && a.version == b.version
      && a.PrivateFields == b.PrivateFields
