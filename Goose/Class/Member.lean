import Goose.Object
import Goose.Signature

namespace Goose

def Class.Constructor.Args {pub : Public} (constrId : pub.ConstructorId) : Type :=
  pub.ConstructorArgs constrId

structure Class.Constructor {sig : Signature} (constrId : sig.pub.ConstructorId) where
  /-- Extra constructor logic. It is combined with auto-generated constructor
      logic to create the complete constructor logic. -/
  extraLogic : constrId.Args → Bool
  /-- Objects created in the constructor call. -/
  created : constrId.Args → Object sig

structure Class.Method {sig : Signature} (methodId : sig.pub.MethodId) where
  /-- Extra method logic. It is combined with auto-generated method logic to
      create the complete method logic. -/
  extraLogic : (self : Object sig) → methodId.Args → Bool
  /-- Objects created in the method call. -/
  created : (self : Object sig) → methodId.Args → List SomeObject

/-- A class member is a method or a constructor. -/
inductive Class.Member (sig : Signature) : Type 1 where
  | constructor (constrId : sig.pub.ConstructorId) (constr : Class.Constructor constrId) : Class.Member sig
  | method (methodId : sig.pub.MethodId) (method : Class.Method methodId) : Class.Member sig

/-- The appData associated with a member call consists of the
    self object's public fields and the member arguments. -/
structure Class.Member.AppData {pub : Public} (memberId : MemberId pub) where
  args : memberId.Args
  -- TODO the types should reflect these three cases:
  -- 1. Class (consumed or created) => only public fields
  -- 2. Member created => only public fields
  -- 3. Member consumed => public fields + method args

structure Class.Member.SomeAppData (pub : Public) where
  {memberId : MemberId pub}
  appData : Class.Member.AppData memberId

instance instMemberSomeAppDataTypeRep {pub : Public}
 : TypeRep (Class.Member.SomeAppData pub) where
  -- TODO: proper type representation
  rep := Rep.atomic "Class.Member.SomeAppData"

instance instMemberAppDataTypeRep {pub : Public} (memberId : MemberId pub)
 : TypeRep (Class.Member.AppData memberId) where
  -- TODO: proper type representation
  rep := Rep.atomic "Class.Member.AppData"

instance instAppDataBeq {pub : Public} (memberId : MemberId pub)
 : BEq (Class.Member.AppData memberId) where
  beq a b :=
    let _ := pub.beqPublicFields
    let _ := memberId.beqArgs
    a.args == b.args

instance instMemberSomeAppDataBeq {pub : Public}
 : BEq (Class.Member.SomeAppData pub) where
  beq a b := beqCast a.appData b.appData

def Class.Method.AppData {pub : Public} (methodId : pub.MethodId) : Type :=
  Member.AppData (MemberId.methodId methodId)

def Class.Constructor.AppData {pub : Public} {constrId : pub.ConstructorId} : Type :=
  Member.AppData (MemberId.constructorId constrId)

end Goose
