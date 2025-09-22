import AVM.Ecosystem.Label
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
  (signatures : Class.Label.MemberId.constructorId constrId |>.Signatures args)
  : Message lab :=
  { id := .classMember (.constructorId constrId)
    contents :=
      { data := .unit
        logicRef := Constructor.Message.logic.{0, 0} constr |>.reference
        vals
        args
        signatures
        recipients := List.Vector.singleton newId }}

def Destructor.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destrId : classId.label.DestructorId}
  (destr : Class.Destructor classId destrId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : destrId.Args.type)
  (signatures : Class.Label.MemberId.destructorId destrId |>.Signatures args)
  : Message lab :=
  { id := .classMember (.destructorId destrId)
    contents :=
      { data := .unit
        logicRef := Destructor.Message.logic.{0, 0} destr |>.reference
        vals
        args
        signatures
        recipients := List.Vector.singleton selfId }}

def Method.message
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  (signatures : Class.Label.MemberId.methodId methodId |>.Signatures args)
  : Message lab :=
  { id := .classMember (.methodId methodId)
    contents :=
      { data := .unit
        logicRef := Method.Message.logic.{0, 0} method |>.reference
        vals
        args
        signatures
        recipients := List.Vector.singleton selfId }}

def Upgrade.message
  {lab : Ecosystem.Label}
  (classId : lab.ClassId)
  (selfId : ObjectId)
  : Message lab :=
  { id := .classMember (classId := classId) .upgradeId
    contents :=
      { data := .unit
        logicRef := Upgrade.Message.logic.{0, 0} classId |>.reference
        Vals := ⟨PUnit⟩
        vals := PUnit.unit
        args := .unit
        signatures f := nomatch f
        recipients := List.Vector.singleton selfId }}

end AVM.Class

namespace AVM.Ecosystem

def MultiMethod.message
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (method : MultiMethod multiId)
  (selves : multiId.Selves)
  (args : multiId.Args.type)
  (vals : (method.body selves args).params.Product)
  : Message lab :=
  let res : MultiMethodResult multiId := method.body selves args |>.value vals
  let data := res.data
  { id := .multiMethodId multiId
    contents :=
      { logicRef := MultiMethod.Message.logic.{0, 0} method data |>.reference
        data
        Vals := ⟨(method.body selves args).params.Product⟩
        vals
        args
        signatures := .unit
        recipients := Label.MultiMethodId.SelvesToVector selves (fun obj => obj.uid) }}
