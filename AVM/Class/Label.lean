import Anoma.Resource
import Prelude
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.FinEnum

namespace AVM.Class

structure DynamicLabel (PrivateFields : Type u) : Type (u + 1) where
  {Label : SomeType}
  mkDynamicLabel : PrivateFields → Label.type

instance DynamicLabel.instInhabited {A : Type u} : Inhabited (DynamicLabel A) where
  default := {Label := ⟨UUnit⟩
              mkDynamicLabel := fun _ => default}


/-- A class label uniquely identifies and specifies a class. The class
    specification provided by a label consists of unique class name, private
    field types, constructor and method ids. -/
structure Label : Type (u + 1) where
  /-- The name of the class uniquely identifying the class.
      Assumption: lab1.name = lab2.name -> lab1 = lab2. -/
  name : String

  PrivateFields : SomeType.{u}

  /-- The dynamic label is used to put dynamic data into the Resource label -/
  DynamicLabel : DynamicLabel.{u} PrivateFields.type := default

  MethodId : Type
  MethodArgs : MethodId -> SomeType.{u}
  [methodsFinite : Fintype MethodId]
  [methodsRepr : Repr MethodId]
  [methodsBEq : BEq MethodId]

  ConstructorId : Type
  ConstructorArgs : ConstructorId -> SomeType.{u}
  [constructorsFinite : Fintype ConstructorId]
  [constructorsRepr : Repr ConstructorId]
  [constructorsBEq : BEq ConstructorId]

  DestructorId : Type := Empty
  DestructorArgs : DestructorId -> SomeType.{u} := fun _ => ⟨UUnit⟩
  [destructorsFinite : Fintype DestructorId]
  [destructorsRepr : Repr DestructorId]
  [destructorsBEq : BEq DestructorId]

inductive Label.MemberId (lab : Label) where
  | constructorId (constrId : lab.ConstructorId) : MemberId lab
  | methodId (methodId : lab.MethodId) : MemberId lab
  | destructorId (destructorId : lab.DestructorId) : MemberId lab

instance Label.MemberId.hasBEq {lab : Label} : BEq (Label.MemberId lab) where
  beq a b :=
    match a, b with
    | constructorId c1, constructorId c2 => lab.constructorsBEq.beq c1 c2
    | constructorId _, _ => false
    | _, constructorId _ => false
    | methodId m1, methodId m2 => lab.methodsBEq.beq m1 m2
    | methodId _, _ => false
    | _, methodId _ => false
    | destructorId c1, destructorId c2 => lab.destructorsBEq.beq c1 c2

instance Label.MemberId.hasTypeRep (lab : Class.Label) : TypeRep (Label.MemberId lab) where
  rep := Rep.composite "AVM.Label.MemberId" [Rep.atomic lab.name]

def Label.ConstructorId.Args {lab : Label} (constrId : lab.ConstructorId) : SomeType :=
  lab.ConstructorArgs constrId

def Label.MethodId.Args {lab : Label} (methodId : lab.MethodId) : SomeType :=
  lab.MethodArgs methodId

def Label.DestructorId.Args {lab : Label} (destructorId : lab.DestructorId) : SomeType :=
  lab.DestructorArgs destructorId

def Label.MemberId.Args {lab : Label.{u}} (memberId : MemberId lab) : SomeType.{u} :=
  match memberId with
  | constructorId c => lab.ConstructorArgs c
  | methodId c => lab.MethodArgs c
  | destructorId c => lab.DestructorArgs c

instance Label.hasTypeRep : TypeRep Label where
  rep := Rep.atomic "AVM.Class.Label"

instance Label.hasBEq : BEq Label where
  beq a b :=
    a.name == b.name
    && a.PrivateFields == b.PrivateFields
