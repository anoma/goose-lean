import Anoma.Resource
import Prelude
import Mathlib.Data.Fintype.Basic

namespace AVM.Class

/-- A class label uniquely identifies and specifies a class. The class
    specification provided by a label consists of unique class name, private and
    public field types, constructor and method ids. -/
structure Label : Type (u + 2) where
  /-- The name of the class uniquely identifying the class.
      Assumption: lab1.name = lab2.name -> lab1 = lab2. -/
  name : String

  PrivateFields : SomeType.{u}
  PublicFields : SomeType.{u}

  MethodId : Type u
  [methodsFinite : Fintype MethodId]
  [methodsRepr : Repr MethodId]
  [methodsBEq : BEq MethodId]
  MethodArgs : MethodId -> SomeType.{u}

  ConstructorId : Type u
  ConstructorArgs : ConstructorId -> SomeType.{u}
  [constructorsFinite : Fintype ConstructorId]
  [constructorsRepr : Repr ConstructorId]
  [constructorsBEq : BEq ConstructorId]

inductive Label.MemberId (lab : Label.{u}) where
  | constructorId (constrId : lab.ConstructorId) : MemberId lab
  | methodId (methodId : lab.MethodId) : MemberId lab
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

def Label.MemberId.Args {lab : Label} (memberId : MemberId lab) : SomeType :=
  match memberId with
  | .constructorId c => lab.ConstructorArgs c
  | .methodId c => lab.MethodArgs c
  | .falseLogicId => ⟨Unit⟩

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
