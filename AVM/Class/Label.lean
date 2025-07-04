import Anoma.Resource
import Prelude
import Mathlib.Data.Fintype.Basic

namespace AVM.Class

structure Private where
  PrivateFields : Type
  [repPrivateFields : TypeRep PrivateFields]
  [beqPrivateFields : BEq PrivateFields]

structure Public where
  PublicFields : Type
  [repPublicFields : TypeRep PublicFields]
  [beqPublicFields : BEq PublicFields]

instance Private.hasBEq : BEq Private where
  beq a b :=
    let _ := a.repPrivateFields
    let _ := b.repPrivateFields
    TypeRep.rep a.PrivateFields == TypeRep.rep b.PrivateFields

instance Public.hasBEq : BEq Public where
  beq a b :=
    let _ := a.repPublicFields
    let _ := b.repPublicFields
    TypeRep.rep a.PublicFields == TypeRep.rep b.PublicFields

structure ArgsType where
  type : Type
  [rep : TypeRep type]
  [beq : BEq type]

/-- A class label uniquely identifies and specifies a class. The class
    specification provided by a label consists of unique class name, private and
    public field types, constructor and method ids. -/
structure Label where
  /-- The name of the class uniquely identifying the class.
      Assumption: lab1.name = lab2.name -> lab1 = lab2. -/
  name : String
  priv : Private
  pub : Public

  MethodId : Type
  [methodsFinite : Fintype MethodId]
  [methodsRepr : Repr MethodId]
  [methodsBEq : BEq MethodId]
  MethodArgsTypes : MethodId -> ArgsType

  ConstructorId : Type
  ConstructorArgsTypes : ConstructorId -> ArgsType
  [constructorsFinite : Fintype ConstructorId]
  [constructorsRepr : Repr ConstructorId]
  [constructorsBEq : BEq ConstructorId]

inductive Label.MemberId (lab : Label) where
  | constructorId : lab.ConstructorId -> MemberId lab
  | methodId : lab.MethodId -> MemberId lab
  | falseLogicId : MemberId lab

instance Label.MemberId.hasBEq {lab : Label} : BEq (Label.MemberId lab) where
  beq a b :=
    match a, b with
    | .constructorId c1, .constructorId c2 => lab.constructorsBEq.beq c1 c2
    | .methodId m1, .methodId m2 => lab.methodsBEq.beq m1 m2
    | .falseLogicId, .falseLogicId => True
    | _, _ => False

def Label.ConstructorArgs {lab : Label} (constrId : lab.ConstructorId) : Type :=
  (lab.ConstructorArgsTypes constrId).type

def Label.ConstructorId.Args {lab : Label} (constrId : lab.ConstructorId) : Type :=
  lab.ConstructorArgs constrId

def Label.MethodArgs {lab : Label} (methodId : lab.MethodId) : Type :=
  (lab.MethodArgsTypes methodId).type

def Label.MethodId.Args {lab : Label} (methodId : lab.MethodId) : Type :=
  lab.MethodArgs methodId

def Label.MemberId.Args {lab : Label} (memberId : MemberId lab) : Type :=
  match memberId with
  | .constructorId c => lab.ConstructorArgs c
  | .methodId c => lab.MethodArgs c
  | .falseLogicId => Unit

instance Label.MemberId.Args.hasBeq {lab : Label} (memberId : MemberId lab) : BEq memberId.Args :=
  match memberId with
  | .constructorId c => (lab.ConstructorArgsTypes c).beq
  | .methodId c => (lab.MethodArgsTypes c).beq
  | .falseLogicId => inferInstanceAs (BEq Unit)

def Label.MemberId.Args.hasTypeRep {lab : Label} (memberId : MemberId lab) : TypeRep memberId.Args :=
  match memberId with
  | .constructorId c => (lab.ConstructorArgsTypes c).rep
  | .methodId c => (lab.MethodArgsTypes c).rep
  | .falseLogicId => inferInstanceAs (TypeRep Unit)

instance {lab : Label} : CoeHead lab.ConstructorId (Label.MemberId lab) where
  coe := Label.MemberId.constructorId

instance {lab : Label} : CoeHead lab.MethodId (Label.MemberId lab) where
  coe := Label.MemberId.methodId

instance Label.hasTypeRep : TypeRep Label where
  rep := Rep.atomic "AVM.Class.Label"

instance Label.hasBEq : BEq Label where
  beq a b :=
    a.name == b.name
    && a.priv == b.priv
    && a.pub == b.pub
