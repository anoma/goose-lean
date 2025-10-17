import AVM.Ecosystem
import AVM.Class
import AVM.Message
import AVM.Class.Translation.Logics

namespace AVM.Class

def Constructor.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  (Vals : SomeType)
  (vals : Vals.type)
  (newId : ObjectId)
  (args : constrId.Args.type)
  (signatures : constrId.Signatures)
  : Message lab :=
  let data : MessageData lab :=
    { id := .classMember (.constructorId constrId)
      logicRef := Constructor.Message.logic.{0, 0} constr |>.reference
      vals
      args
      recipients := [newId] }
  { data, signatures }

def Destructor.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destrId : classId.label.DestructorId}
  (destr : Class.Destructor classId destrId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : destrId.Args.type)
  (signatures : destrId.Signatures)
  : Message lab :=
  let data : MessageData lab :=
    { id := .classMember (.destructorId destrId)
      logicRef := Destructor.Message.logic.{0, 0} destr |>.reference
      vals
      args
      recipients := [selfId] }
  { data, signatures }

def Method.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  (signatures : methodId.Signatures)
  : Message lab :=
  let data : MessageData lab :=
    { id := .classMember (.methodId methodId)
      logicRef := Method.Message.logic.{0, 0} method |>.reference
      vals
      args
      recipients := [selfId] }
  { data, signatures }

def Upgrade.message
  {lab : Ecosystem.Label}
  (classId : lab.ClassId)
  (selfId : ObjectId)
  : Message lab :=
  let data : MessageData lab :=
    { id := .classMember (classId := classId) .upgradeId
      logicRef := Upgrade.Message.logic.{0, 0} classId |>.reference
      Vals := ⟨PUnit⟩
      vals := PUnit.unit
      args := .unit
      recipients := [selfId] }
  { data, signatures := fun f => nomatch f}

end AVM.Class

namespace AVM.Ecosystem

def MultiMethod.message
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (method : MultiMethod multiId)
  (selves : multiId.Selves)
  (args : multiId.Args.type)
  (signatures : multiId.Signatures)
  (vals : (method.body selves args).params.Product)
  (data : MultiMethodData)
  (rands : MultiMethodRandoms data)
  : Message lab :=
  let data : MessageData lab :=
    { id := .multiMethodId multiId
      logicRef := MultiMethod.Message.logic.{0, 0} method |>.reference
      Vals := ⟨(method.body selves args).params.Product⟩
      vals
      args
      recipients :=
        (Label.MultiMethodId.SelvesToVector selves (fun obj => obj.uid) |>.toList)
          ++ rands.constructedNonces.toList.map (·.value) }
  { data, signatures }
