import Anoma.Resource
import Prelude
import Mathlib.Data.Fintype.Basic

namespace Goose.Class

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

structure Label where
  priv : Private
  pub : Public
  name : String

  MethodId : Type
  MethodArgs : MethodId -> Type
  repMethodArgs (m : MethodId) : TypeRep (MethodArgs m)
  beqMethodArgs (m : MethodId) : BEq (MethodArgs m)
  [methodsFinite : Fintype MethodId]
  [methodsRepr : Repr MethodId]

  ConstructorId : Type
  ConstructorArgs : ConstructorId -> Type
  repConstructorArgs (m : ConstructorId) : TypeRep (ConstructorArgs m)
  beqConstructorArgs (m : ConstructorId) : BEq (ConstructorArgs m)
  [constructorsFinite : Fintype ConstructorId]
  [constructorsRepr : Repr ConstructorId]

inductive MemberId (lab : Label) where
  | constructorId : lab.ConstructorId -> MemberId lab
  | methodId : lab.MethodId -> MemberId lab

def Label.ConstructorId.Args {lab : Label} (constrId : lab.ConstructorId) : Type :=
  lab.ConstructorArgs constrId

def Label.MethodId.Args {lab : Label} (methodId : lab.MethodId) : Type :=
  lab.MethodArgs methodId

def MemberId.Args {lab : Label} (memberId : MemberId lab) : Type :=
  match memberId with
    | .constructorId c => lab.ConstructorArgs c
    | .methodId c => lab.MethodArgs c

def MemberId.beqArgs {lab : Label} (memberId : MemberId lab) : BEq memberId.Args :=
  match memberId with
    | .constructorId c => lab.beqConstructorArgs c
    | .methodId c => lab.beqMethodArgs c

instance {lab : Label} : CoeHead lab.ConstructorId (MemberId lab) where
  coe := MemberId.constructorId

instance {lab : Label} : CoeHead lab.MethodId (MemberId lab) where
  coe := MemberId.methodId

instance Label.hasTypeRep : TypeRep Label where
  rep := Rep.atomic "Goose.Class.Label"

instance Label.hasBEq : BEq Label where
  beq a b :=
    a.priv == b.priv
    && a.pub == b.pub
    && a.name == b.name
