import AVM.Ecosystem.Label
import AVM.Class
import AVM.Message

namespace AVM.Class

def Constructor.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (_constr : Class.Constructor classId constrId)
  (Vals : SomeType)
  (vals : Vals.type)
  (newId : ObjectId)
  (args : constrId.Args.type)
  : Message classId.label :=
  { id := Label.MemberId.constructorId constrId,
    vals,
    args,
    recipient := newId }

def Destructor.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (_destructor : Class.Destructor classId destructorId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : destructorId.Args.type)
  : Message classId.label :=
  { id := Label.MemberId.destructorId destructorId,
    vals,
    args,
    recipient := selfId }

def Method.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (_method : Class.Method classId methodId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  : Message classId.label :=
  { id := Label.MemberId.methodId methodId,
    vals,
    args,
    recipient := selfId }
