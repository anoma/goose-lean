import Anoma.Resource
import Prelude
import Mathlib.Data.Fintype.Basic

namespace Goose

structure Private where
  PrivateFields : Type
  [repPrivateFields : TypeRep PrivateFields]
  [beqPrivateFields : BEq PrivateFields]

structure Public where
  PublicFields : Type
  [repPublicFields : TypeRep PublicFields]
  [beqPublicFields : BEq PublicFields]

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

instance instBeqPrivate : BEq Private where
  beq a b :=
    let _ := a.repPrivateFields
    let _ := b.repPrivateFields
    TypeRep.rep a.PrivateFields == TypeRep.rep b.PrivateFields

instance instBeqPublic : BEq Public where
  beq a b :=
    let _ := a.repPublicFields
    let _ := b.repPublicFields
    TypeRep.rep a.PublicFields == TypeRep.rep b.PublicFields

inductive MemberId (pub : Public) where
  | constructorId : pub.ConstructorId -> MemberId pub
  | methodId : pub.MethodId -> MemberId pub

def Public.ConstructorId.Args {pub : Public} (constrId : pub.ConstructorId) : Type :=
  pub.ConstructorArgs constrId

def Public.MethodId.Args {pub : Public} (methodId : pub.MethodId) : Type :=
  pub.MethodArgs methodId

def MemberId.Args {pub : Public} (memberId : MemberId pub) : Type :=
  match memberId with
    | constructorId c => pub.ConstructorArgs c
    | methodId c => pub.MethodArgs c

def MemberId.beqArgs {pub : Public} (memberId : MemberId pub) : BEq memberId.Args :=
  match memberId with
    | constructorId c => pub.beqConstructorArgs c
    | methodId c => pub.beqMethodArgs c

instance {pub : Public} : CoeHead pub.ConstructorId (MemberId pub) where
  coe := MemberId.constructorId

instance {pub : Public} : CoeHead pub.MethodId (MemberId pub) where
  coe := MemberId.methodId

-- TODO rename to something that does not conflict with authorization
structure Signature where
  priv : Private
  pub : Public
  classLabel : String
deriving BEq
