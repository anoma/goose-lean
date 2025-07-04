import AVM.Object
import AVM.Class.Label

namespace AVM.Class

def Constructor.Args {lab : Label} (constrId : lab.ConstructorId) : Type :=
  lab.ConstructorArgs constrId

structure Constructor {lab : Label} (constrId : lab.ConstructorId) where
  /-- Extra constructor logic. The constructor invariant is combined with
      auto-generated constructor body constraints to create the constructor logic. -/
  invariant : constrId.Args → Bool
  /-- Objects created in the constructor call. -/
  created : constrId.Args → Object lab

structure Method {lab : Label} (methodId : lab.MethodId) where
  /-- Extra method logic. The method invariant is combined with auto-generated
      method body constraints to create the method logic. -/
  invariant : (self : Object lab) → methodId.Args → Bool
  /-- Objects created in the method call. -/
  created : (self : Object lab) → methodId.Args → List SomeObject

/-- A class member is a method or a constructor. -/
inductive Member (lab : Label) : Type 1 where
  | constructor (constrId : lab.ConstructorId) (constr : Constructor constrId) : Member lab
  | method (methodId : lab.MethodId) (method : Method methodId) : Member lab

/-- The appData associated with a member call consists of the
    self object's public fields and the member arguments. -/
structure Member.AppData {lab : Label} (memberId : MemberId lab) where
  args : memberId.Args

structure Member.SomeAppData (lab : Label) where
  {memberId : MemberId lab}
  appData : Member.AppData memberId

instance Member.SomeAppData.hasTypeRep {lab : Label}
 : TypeRep (Member.SomeAppData lab) where
  -- TODO: proper type representation
  rep := Rep.atomic "Class.Member.SomeAppData"

instance Member.AppData.hasTypeRep {lab : Label} (memberId : MemberId lab)
 : TypeRep (Member.AppData memberId) where
  -- TODO: proper type representation
  rep := Rep.atomic "Class.Member.AppData"

instance AppData.hasBeq {lab : Label} (memberId : MemberId lab)
 : BEq (Member.AppData memberId) where
  beq a b :=
    let _ := lab.pub.beqPublicFields
    let _ := memberId.beqArgs
    a.args == b.args

instance Member.SomeAppData.hasBeq {lab : Label}
 : BEq (Member.SomeAppData lab) where
  beq a b := beqCast a.appData b.appData

def Method.AppData {lab : Label} (methodId : lab.MethodId) : Type :=
  Member.AppData (MemberId.methodId methodId)

def Constructor.AppData {lab : Label} {constrId : lab.ConstructorId} : Type :=
  Member.AppData (MemberId.constructorId constrId)
