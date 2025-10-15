import AVM.Ecosystem.Label
import AVM.Class
import AVM.Message
import AVM.Class.Translation.Logics

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
  (signatures : Class.Label.MemberId.constructorId constrId |>.Signatures args)
  : Message lab :=
  { id := .classMember (.constructorId constrId)
    logicRef := Logic.trivialLogicRef
    vals
    args
    signatures
    recipients := [newId] }

def Destructor.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destrId : classId.label.DestructorId}
  (_destr : Class.Destructor classId destrId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : destrId.Args.type)
  (signatures : Class.Label.MemberId.destructorId destrId |>.Signatures args)
  : Message lab :=
  { id := .classMember (.destructorId destrId)
    logicRef := Logic.trivialLogicRef
    vals
    args
    signatures
    recipients := [selfId] }

def Method.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (_method : Class.Method classId methodId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  (signatures : Class.Label.MemberId.methodId methodId |>.Signatures args)
  : Message lab :=
  { id := .classMember (.methodId methodId)
    logicRef := Logic.trivialLogicRef
    vals
    args
    signatures
    recipients := [selfId] }

def Upgrade.message
  {lab : Ecosystem.Label}
  (classId : lab.ClassId)
  (selfId : ObjectId)
  : Message lab :=
  { id := .classMember (classId := classId) .upgradeId
    logicRef := Logic.trivialLogicRef
    Vals := ⟨PUnit⟩
    vals := PUnit.unit
    args := .unit
    signatures f := nomatch f
    recipients := [selfId] }

end AVM.Class

namespace AVM.Ecosystem

def MultiMethod.message
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (method : MultiMethod multiId)
  (selves : multiId.Selves)
  (args : multiId.Args.type)
  (signatures : multiId.Signatures args)
  (vals : (method.body selves args).params.Product)
  (data : MultiMethodData)
  (rands : MultiMethodRandoms data)
  : Message lab :=
  { id := .multiMethodId multiId
    logicRef := Logic.trivialLogicRef
    Vals := ⟨(method.body selves args).params.Product⟩
    vals
    args
    signatures
    recipients :=
      (Label.MultiMethodId.SelvesToVector selves (fun obj => obj.uid) |>.toList)
        ++ rands.constructedNonces.toList.map (·.value) }
