import Anoma.Resource
import Prelude
import Mathlib.Data.Fintype.Basic

namespace AVM.Class

structure DynamicLabel (PrivateFields : Type u) : Type (u + 1) where
  {Label : SomeType}
  mkDynamicLabel : PrivateFields -> Label.type

instance DynamicLabel.instInhabited {A : Type u} : Inhabited (DynamicLabel A) where
  default := {Label := ⟨UUnit⟩
              mkDynamicLabel := fun _ => default}

/-- A class label uniquely identifies and specifies a class. The class
    specification provided by a label consists of unique class name, private and
    public field types, constructor and method ids. -/
structure Label : Type (max u v + 1) where
  /-- The name of the class uniquely identifying the class.
      Assumption: lab1.name = lab2.name -> lab1 = lab2. -/
  name : String

  PrivateFields : SomeType.{u}
  PublicFields : SomeType.{v}

  /-- The dynamic label is used to put dynamic data into the Resource label -/
  DynamicLabel : DynamicLabel.{u} PrivateFields.type := default

  MethodId : Type
  [methodsFinite : Fintype MethodId]
  [methodsRepr : Repr MethodId]
  [methodsBEq : BEq MethodId]
  MethodArgs : MethodId -> SomeType.{u}

  ConstructorId : Type
  [constructorsFinite : Fintype ConstructorId]
  [constructorsRepr : Repr ConstructorId]
  [constructorsBEq : BEq ConstructorId]
  ConstructorArgs : ConstructorId -> SomeType.{u}

inductive Label.MemberId (lab : Label.{u}) where
  | constructorId (constrId : lab.ConstructorId) : MemberId lab
  | methodId (methodId : lab.MethodId) : MemberId lab
  /-- Signifies an "always false" member logic. This is used for the member
    logic field of app data, in the created case. It is important that "dummy"
    member logic indicator for the created case always returns false – otherwise
    one could circumvent method logic checks by providing the dummy member logic
    indicator. This could also be represented by an `Option` type in app data,
    but having explicit `falseLogicId` makes its intended behaviour clear. -/
  | falseLogicId : MemberId lab

instance Label.MemberId.hasBEq {lab : Label} : BEq (Label.MemberId lab) where
  beq a b :=
    match a, b with
    | .constructorId c1, .constructorId c2 => lab.constructorsBEq.beq c1 c2
    | .methodId m1, .methodId m2 => lab.methodsBEq.beq m1 m2
    | .falseLogicId, .falseLogicId => true
    | _, _ => false

def Label.ConstructorId.Args {lab : Label} (constrId : lab.ConstructorId) : SomeType :=
  lab.ConstructorArgs constrId

def Label.MethodId.Args {lab : Label} (methodId : lab.MethodId) : SomeType :=
  lab.MethodArgs methodId

def Label.MemberId.Args {lab : Label.{u}} (memberId : MemberId lab) : SomeType.{u} :=
  match memberId with
  | .constructorId c => lab.ConstructorArgs c
  | .methodId c => lab.MethodArgs c
  | .falseLogicId => ⟨UUnit⟩

instance {lab : Label} : CoeHead lab.ConstructorId (Label.MemberId lab) where
  coe := Label.MemberId.constructorId

instance {lab : Label} : CoeHead lab.MethodId (Label.MemberId lab) where
  coe := Label.MemberId.methodId

instance Label.hasTypeRep : TypeRep Label where
  rep := Rep.atomic "AVM.Class.Label"

instance Label.hasBEq : BEq Label where
  beq a b :=
    a.name == b.name
    && a.PrivateFields == b.PrivateFields
    && a.PublicFields == b.PublicFields
