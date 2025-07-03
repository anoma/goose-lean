import Goose.Object
import Goose.Signature

namespace Goose

def Class.Constructor.Args {sig : Signature} (constrId : sig.ConstructorId) : Type :=
  sig.ConstructorArgs constrId

structure Class.Constructor {sig : Signature} (constrId : sig.ConstructorId) where
  /-- Extra constructor logic. It is combined with auto-generated constructor
      logic to create the complete constructor logic. -/
  extraLogic : constrId.Args → Bool
  /-- Objects created in the constructor call. -/
  created : constrId.Args → Object sig

structure Class.Method {sig : Signature} (methodId : sig.MethodId) where
  /-- Extra method logic. It is combined with auto-generated method logic to
      create the complete method logic. -/
  extraLogic : (self : Object sig) → methodId.Args → Bool
  /-- Objects created in the method call. -/
  created : (self : Object sig) → methodId.Args → List SomeObject

/-- A class member is a method or a constructor. -/
inductive Class.Member (sig : Signature) : Type 1 where
  | constructor (constrId : sig.ConstructorId) (constr : Class.Constructor constrId) : Class.Member sig
  | method (methodId : sig.MethodId) (method : Class.Method methodId) : Class.Member sig

/-- The appData associated with a member call consists of the
    self object's public fields and the member arguments. -/
structure Class.Member.AppData {sig : Signature} (memberId : MemberId sig) where
  args : memberId.Args

structure Class.Member.SomeAppData (sig : Signature) where
  {memberId : MemberId sig}
  appData : Class.Member.AppData memberId

instance instMemberSomeAppDataTypeRep {sig : Signature}
 : TypeRep (Class.Member.SomeAppData sig) where
  -- TODO: proper type representation
  rep := Rep.atomic "Class.Member.SomeAppData"

instance instMemberAppDataTypeRep {sig : Signature} (memberId : MemberId sig)
 : TypeRep (Class.Member.AppData memberId) where
  -- TODO: proper type representation
  rep := Rep.atomic "Class.Member.AppData"

instance instAppDataBeq {sig : Signature} (memberId : MemberId sig)
 : BEq (Class.Member.AppData memberId) where
  beq a b :=
    let _ := sig.pub.beqPublicFields
    let _ := memberId.beqArgs
    a.args == b.args

instance instMemberSomeAppDataBeq {sig : Signature}
 : BEq (Class.Member.SomeAppData sig) where
  beq a b := beqCast a.appData b.appData

def Class.Method.AppData {sig : Signature} (methodId : sig.MethodId) : Type :=
  Member.AppData (MemberId.methodId methodId)

def Class.Constructor.AppData {sig : Signature} {constrId : sig.ConstructorId} : Type :=
  Member.AppData (MemberId.constructorId constrId)

end Goose
