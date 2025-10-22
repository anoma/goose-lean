import AVM.Ecosystem
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
  (signatures : MessageData lab → List Signature)
  : Message lab :=
  let data : MessageData lab :=
    { id := .classMember (.constructorId constrId)
      vals
      args
      recipients := [newId] }
  { data,
    signatures := signatures data }

def Destructor.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destrId : classId.label.DestructorId}
  (_destr : Class.Destructor classId destrId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : destrId.Args.type)
  (signatures : MessageData lab → List Signature)
  : Message lab :=
  let data : MessageData lab :=
    { id := .classMember (.destructorId destrId)
      vals
      args
      recipients := [selfId] }
  { data,
    signatures := signatures data }

def Method.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (_method : Class.Method classId methodId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  (signatures : MessageData lab → List Signature)
  : Message lab :=
  let data : MessageData lab :=
    { id := .classMember (.methodId methodId)
      vals
      args
      recipients := [selfId] }
  { data,
    signatures := signatures data }

def Upgrade.message
  {lab : Ecosystem.Label}
  (classId : lab.ClassId)
  (selfId : ObjectId)
  : Message lab :=
  let data : MessageData lab :=
    { id := .classMember (classId := classId) .upgradeId
      Vals := ⟨PUnit⟩
      vals := PUnit.unit
      args := .unit
      recipients := [selfId] }
  { data, signatures := []}

end AVM.Class

namespace AVM.Ecosystem

def MultiMethod.message
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (method : MultiMethod multiId)
  (selves : multiId.Selves)
  (args : multiId.Args.type)
  (signatures : MessageData lab → List Signature)
  (vals : (method.body selves args).params.Product)
  (data : MultiMethodData)
  (rands : MultiMethodRandoms data)
  : Message lab :=
  let data : MessageData lab :=
    { id := .multiMethodId multiId
      Vals := ⟨(method.body selves args).params.Product⟩
      vals
      args
      recipients :=
        (Label.MultiMethodId.SelvesToVector selves (fun obj => obj.uid) |>.toList)
          ++ rands.constructedNonces.toList.map (·.value) }
  { data,
    signatures := signatures data }
