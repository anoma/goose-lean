import AVM.Ecosystem
import AVM.Ecosystem.AppData
import Prelude
import AVM.Class.Translation
import AVM.Logic
import AVM.Action

namespace AVM.Ecosystem

open AVM.Action

def MultiMethod.parseObjectArgs
  {lab : Ecosystem.Label}
  (consumed : List Anoma.Resource)
  (funId : lab.MultiMethodId)
  : Option funId.Selves
  :=
  let try consumedVec : Vector Anoma.Resource funId.numObjectArgs := consumed.toSizedVector
  let mkConsumedObject (a : funId.ObjectArgNames) : Option (Object a.classId.label) := Object.fromResource (consumedVec.get a.ix)
  @FinEnum.decImageOption'
    funId.ObjectArgNames
    (lab.objectArgNamesEnum funId)
    (fun a => Object a.classId.label)
    mkConsumedObject

def MultiMethod.logic
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Logic.Args)
  (funId : lab.MultiMethodId)
  (funData : MultiMethodData)
  (fargs : funId.Args.type)
  : Bool := sorry

private def logic
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Logic.Args)
  : Bool := sorry

def MultiMethod.message
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (_method : Ecosystem.MultiMethod multiId)
  (Vals : SomeType)
  (vals : Vals.type)
  (selfId : ObjectId)
  (args : multiId.Args.type)
  : Message lab :=
  { id := .multiMethodId multiId,
    vals,
    args,
    recipient := sorry }

end AVM.Ecosystem

namespace AVM

set_option pp.universes true

mutual

partial def Program.tasks.{u}
  {α}
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (prog : Program lab α)
  (vals : prog.params.Product)
  : List Task :=
  match prog with
  | .constructor classId constrId args next =>
    let constr := eco.classes classId |>.constructors constrId
    let task := constr.task eco args
    let ⟨newId, vals'⟩ := vals
    task :: Program.tasks eco (next newId) vals'
  | .destructor classId destrId selfId args next =>
    let destr := eco.classes classId |>.destructors destrId
    let task := destr.task eco selfId args
    task :: Program.tasks eco next vals
  | .method classId methodId selfId args next =>
    let method := eco.classes classId |>.methods methodId
    let task := method.task eco selfId args
    task :: Program.tasks eco next vals
  | .multiMethod methodId selvesIds args next =>
    let task := methodId.task eco selvesIds args
    task :: Program.tasks eco next vals
  | .fetch _ next =>
    let ⟨obj, vals'⟩ := vals
    Program.tasks eco (next obj) vals'
  | .return _ => []

/-- Creates a Task for a given object constructor. -/
partial def Class.Constructor.task.{u}
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  (args : constrId.Args.type)
  : Task.{u} :=
  let bodyParams := (constr.body args).params
  let params : Program.Parameters := Program.Parameters.genId (fun _ => bodyParams)
  Task.absorbParams params fun ⟨newId, vals⟩ =>
    let body := constr.body args
    let tasks := Program.tasks eco body vals
    let newObjData : ObjectData classId.label := body.returnValue vals
    let newObj : SomeObject :=
      let obj : Object classId.label :=
        { uid := newId,
          nonce := ⟨newId⟩,
          data := newObjData }
      obj.toSomeObject
    let consumedObj := newObj.toConsumable (ephemeral := true)
    let createdObjects : List CreatedObject :=
      [CreatedObject.fromSomeObject newObj (ephemeral := false)]
    Task.composeWithMessage (constr.message ⟨bodyParams.Product⟩ vals newId args) tasks [consumedObj] createdObjects

/-- Creates a Task for a given object destructor. -/
partial def Class.Destructor.task.{u}
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor classId destructorId)
  (selfId : ObjectId)
  (args : destructorId.Args.type)
  : Task.{u} :=
  let consumedObjectId : TypedObjectId := ⟨classId.label, selfId⟩
  let bodyParams (self : Object classId.label) := (destructor.body self args).params
  let params := Program.Parameters.fetch consumedObjectId bodyParams
  Task.absorbParams params fun ⟨self, vals⟩ =>
    let tasks : List Task := Program.tasks eco (destructor.body self args) vals
    let consumedObj := self.toSomeObject.toConsumable (ephemeral := false)
    let createdObjects : List CreatedObject :=
      [{ uid := self.uid,
         data := self.data,
         ephemeral := true }]
    Task.composeWithMessage (destructor.message ⟨(bodyParams self).Product⟩ vals selfId args) tasks [consumedObj] createdObjects

partial def Class.Method.task.{u}
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (selfId : ObjectId)
  (args : methodId.Args.type)
  : Task.{u} :=
  let consumedObjectId : TypedObjectId := ⟨classId.label, selfId⟩
  let bodyParams (self : Object classId.label) := (method.body self args).params
  let params := Program.Parameters.fetch consumedObjectId bodyParams
  Task.absorbParams params fun ⟨self, vals⟩ =>
    let body := method.body self args
    let tasks : List Task := Program.tasks eco body vals
    let consumedObj := self.toSomeObject.toConsumable (ephemeral := false)
    let obj := (body.returnValue vals).toSomeObject
    let createdObjects : List CreatedObject :=
      [{ uid := obj.object.uid,
         data := obj.object.data,
         ephemeral := false }]
    Task.composeWithMessage (method.message ⟨(bodyParams self).Product⟩ vals selfId args) tasks [consumedObj] createdObjects

partial def Ecosystem.Label.MultiMethodId.task.{u}
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  {methodId : lab.MultiMethodId}
  (selvesIds : methodId.SelvesIds)
  (args : methodId.Args.type)
  : Task.{u} :=
  let method := eco.multiMethods methodId
  let bodyParams (selves : methodId.Selves) : Program.Parameters := method.body selves args |>.params
  let params : Program.Parameters := Program.Parameters.fetchSelves (multiId := methodId) selvesIds bodyParams
  Task.absorbParams params fun (selvesAndVals : params.Product) =>
    -- let body := method.body ?self args
    -- let tasks : List Task := Program.tasks eco body ?vals
    -- let consumedObj := self.toSomeObject.toConsumable (ephemeral := false)
    -- let obj := (body.returnValue vals).toSomeObject
    -- let createdObjects : List CreatedObject :=
    --   [{ uid := obj.object.uid,
    --      data := obj.object.data,
    --      ephemeral := false }]
    -- Task.composeWithMessage (method.message ⟨(bodyParams self).Product⟩ vals selfId args) tasks [consumedObj] createdObjects
    sorry

end -- mutual
