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

-- TODO rename to something that does not conflict with authorization
structure Signature where
  priv : Private
  pub : Public
  classLabel : String

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

inductive MemberId (sig : Signature) where
  | constructorId : sig.ConstructorId -> MemberId sig
  | methodId : sig.MethodId -> MemberId sig

def Signature.ConstructorId.Args {sig : Signature} (constrId : sig.ConstructorId) : Type :=
  sig.ConstructorArgs constrId

def Signature.MethodId.Args {sig : Signature} (methodId : sig.MethodId) : Type :=
  sig.MethodArgs methodId

def MemberId.Args {sig : Signature} (memberId : MemberId sig) : Type :=
  match memberId with
    | constructorId c => sig.ConstructorArgs c
    | methodId c => sig.MethodArgs c

def MemberId.beqArgs {sig : Signature} (memberId : MemberId sig) : BEq memberId.Args :=
  match memberId with
    | constructorId c => sig.beqConstructorArgs c
    | methodId c => sig.beqMethodArgs c

instance {sig : Signature} : CoeHead sig.ConstructorId (MemberId sig) where
  coe := MemberId.constructorId

instance {sig : Signature} : CoeHead sig.MethodId (MemberId sig) where
  coe := MemberId.methodId
