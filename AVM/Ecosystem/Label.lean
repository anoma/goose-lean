import AVM.Class.Label
import AVM.Object

namespace AVM.Ecosystem

structure Label : Type 1 where
  name : String

  ClassId : Type
  classLabel : ClassId → Class.Label
  [classesEnum : FinEnum ClassId]
  [classesRepr : Repr ClassId]
  [classesBEq : BEq ClassId]

def Label.classId (l : Label) (clab : Class.Label) : Option l.ClassId :=
  l.classesEnum.toList.find? (fun b => l.classLabel b == clab)

end AVM.Ecosystem

namespace AVM.Ecosystem.Label

/-- Singleton ecosystem: An ecosystem with a single class, no functions and no intents -/
def singleton (l : Class.Label) : Ecosystem.Label where
  name := l.name

  ClassId := PUnit
  classLabel := fun _ => l

def ClassId.label {lab : Ecosystem.Label} (classId : lab.ClassId) : Class.Label :=
  lab.classLabel classId

def ClassId.MemberId {lab : Ecosystem.Label} (c : lab.ClassId) := c.label.MemberId

instance ClassId.MemberId.hasTypeRep {lab : Ecosystem.Label} {c : lab.ClassId} : TypeRep c.MemberId := Class.Label.MemberId.hasTypeRep c.label

instance ClassId.MemberId.hasBEq {lab : Ecosystem.Label} {c : lab.ClassId} : BEq c.MemberId := Class.Label.MemberId.hasBEq

instance {lab : Ecosystem.Label} {classId : lab.ClassId}
  : CoeHead classId.label.ConstructorId classId.MemberId where
  coe := .constructorId

instance {lab : Ecosystem.Label} {classId : lab.ClassId}
  : CoeHead classId.label.MethodId classId.MemberId where
  coe := .methodId

instance {lab : Ecosystem.Label} {classId : lab.ClassId}
  : CoeHead classId.label.DestructorId classId.MemberId where
  coe := .destructorId
