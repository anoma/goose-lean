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

structure Label where
  priv : Private
  pub : Public
  name : String

  MethodId : Type
  [methodsFinite : Fintype MethodId]
  [methodsRepr : Repr MethodId]
  MethodArgsTypes : MethodId -> ArgsType

  ConstructorId : Type
  ConstructorArgsTypes : ConstructorId -> ArgsType
  [constructorsFinite : Fintype ConstructorId]
  [constructorsRepr : Repr ConstructorId]

inductive MemberId (lab : Label) where
  | constructorId : lab.ConstructorId -> MemberId lab
  | methodId : lab.MethodId -> MemberId lab

def Label.ConstructorArgs {lab : Label} (constrId : lab.ConstructorId) : Type :=
  (lab.ConstructorArgsTypes constrId).type

def Label.ConstructorId.Args {lab : Label} (constrId : lab.ConstructorId) : Type :=
  lab.ConstructorArgs constrId

def Label.MethodArgs {lab : Label} (methodId : lab.MethodId) : Type :=
  (lab.MethodArgsTypes methodId).type

def Label.MethodId.Args {lab : Label} (methodId : lab.MethodId) : Type :=
  lab.MethodArgs methodId

def MemberId.Args {lab : Label} (memberId : MemberId lab) : Type :=
  match memberId with
    | .constructorId c => lab.ConstructorArgs c
    | .methodId c => lab.MethodArgs c

def MemberId.beqArgs {lab : Label} (memberId : MemberId lab) : BEq memberId.Args :=
  match memberId with
    | constructorId c => (lab.ConstructorArgsTypes c).beq
    | methodId c => (lab.MethodArgsTypes c).beq

instance {lab : Label} : CoeHead lab.ConstructorId (MemberId lab) where
  coe := MemberId.constructorId

instance {lab : Label} : CoeHead lab.MethodId (MemberId lab) where
  coe := MemberId.methodId

instance Label.hasTypeRep : TypeRep Label where
  rep := Rep.atomic "AVM.Class.Label"

instance Label.hasBEq : BEq Label where
  beq a b :=
    a.priv == b.priv
    && a.pub == b.pub
    && a.name == b.name
