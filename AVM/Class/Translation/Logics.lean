import AVM.Class
import AVM.Message
import AVM.Logic
import AVM.Ecosystem

namespace AVM.Logic

def classLogicRef {lab : Ecosystem.Label} (classId : lab.ClassId) : Anoma.LogicRef :=
  classId.label.logicRef

def constructorLogicRef {lab : Ecosystem.Label} {classId : lab.ClassId} (constrId : classId.label.ConstructorId) : Anoma.LogicRef :=
  ⟨s!"AVM.Class.{classId.label.name}.Constructor.{@repr _ classId.label.constructorsRepr constrId}"⟩

def destructorLogicRef {lab : Ecosystem.Label} {classId : lab.ClassId} (destrId : classId.label.DestructorId) : Anoma.LogicRef :=
  ⟨s!"AVM.Class.{classId.label.name}.Destructor.{@repr _ classId.label.destructorsRepr destrId}"⟩

def methodLogicRef {lab : Ecosystem.Label} {classId : lab.ClassId} (methodId : classId.label.MethodId) : Anoma.LogicRef :=
  ⟨s!"AVM.Class.{classId.label.name}.Method.{@repr _ classId.label.methodsRepr methodId}"⟩

def upgradeLogicRef {lab : Ecosystem.Label} (classId : lab.ClassId) : Anoma.LogicRef :=
  ⟨s!"AVM.Class.{classId.label.name}.Upgrade"⟩

def multiMethodLogicRef {lab : Ecosystem.Label} (multiId : lab.MultiMethodId) : Anoma.LogicRef :=
  ⟨s!"AVM.MultiMethod.{@repr _ lab.multiMethodsRepr multiId}"⟩

end AVM.Logic

namespace AVM.Program

structure MessageValue (lab : Ecosystem.Label) where
  id : lab.MemberId
  args : id.Args.type
  logicRef : Anoma.LogicRef

def messageValues
  {lab : Ecosystem.Label}
  {α : Type u}
  (prog : Program lab.toScope α)
  (vals : prog.params.Product)
  : List (MessageValue lab) :=
  match prog with
  | .constructor _ _ constrId args _ next =>
    let msgData : MessageValue lab :=
      { id := .classMember (.constructorId constrId)
        args := args,
        logicRef := Logic.constructorLogicRef constrId }
    let ⟨objId, vals'⟩ := vals
    msgData :: Program.messageValues (next objId) vals'
  | .destructor _ _ destrId _ args _ next =>
    let msgData : MessageValue lab :=
      { id := .classMember (.destructorId destrId)
        args := args,
        logicRef := Logic.destructorLogicRef destrId }
    msgData :: Program.messageValues next vals
  | .method _ _ methodId _ args _ next =>
    let msgData : MessageValue lab :=
      { id := .classMember (.methodId methodId)
        args := args,
        logicRef := Logic.methodLogicRef methodId }
    msgData :: Program.messageValues next vals
  | .multiMethod _ mid _ args _ next =>
    let msgData : MessageValue lab :=
      { id := .multiMethodId mid
        args := args,
        logicRef := Logic.multiMethodLogicRef mid }
    msgData :: Program.messageValues next vals
  | .upgrade _ cid _ _ next =>
    let msgData : MessageValue lab :=
      { id := .classMember (classId := cid) .upgradeId
        args := PUnit.unit,
        logicRef := Logic.upgradeLogicRef cid }
    msgData :: Program.messageValues next vals
  | .fetch _ next =>
    let ⟨obj, vals'⟩ := vals
    Program.messageValues (next obj) vals'
  | .return _ => []

end AVM.Program

namespace AVM.Logic

def checkMessageResourceValues {lab : Ecosystem.Label} (vals : List (Program.MessageValue lab)) (resMsgs : List Anoma.Resource) : Bool :=
  vals.length == resMsgs.length &&
  List.all₂
    (fun val res =>
      let try msg : Message lab := Message.fromResource res
      msg.id == val.id && msg.args === val.args && msg.logicRef == val.logicRef)
    vals
    resMsgs

end AVM.Logic

namespace AVM.Class

/-- Creates a message logic function for a given constructor. -/
private def Constructor.Message.logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  check h : msg.id == .classMember (Label.MemberId.constructorId constrId)
  let argsData : constrId.Args.type := cast (by simp! [eq_of_beq h]) msg.args
  let signatures : constrId.Signatures argsData := cast (by grind only) msg.signatures
  let body := constr.body argsData
  let try vals : body.params.Product := tryCast msg.vals
  let newObjData := body.value vals
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! [newObjRes] := createdResObjs
  let uid : ObjectId := newObjRes.nonce.value
  let messageValues := Program.messageValues body vals
  let createdResMsgs := Logic.selectMessageResources args.created
  Logic.checkMessageResourceValues messageValues createdResMsgs
    && Logic.checkResourceValues [newObjData.toObjectValue uid] consumedResObjs
    && Logic.checkResourceValues [newObjData.toObjectValue uid] createdResObjs
    && Logic.checkResourcesEphemeral consumedResObjs
    && Logic.checkResourcesPersistent createdResObjs
    && constr.invariant argsData signatures

/-- Creates a message logic function for a given destructor. -/
private def Destructor.Message.logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor classId destructorId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  check h : msg.id == .classMember (Label.MemberId.destructorId destructorId)
  let argsData := cast (by simp! [eq_of_beq h]) msg.args
  let signatures : destructorId.Signatures argsData := cast (by grind only) msg.signatures
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! [selfRes] := consumedResObjs
  let try selfObj : Object classId := Object.fromResource selfRes
  let body := destructor.body selfObj argsData
  let try vals : body.params.Product := tryCast msg.vals
  let messageValues := Program.messageValues body vals
  let createdResMsgs := Logic.selectMessageResources args.created
  Logic.checkMessageResourceValues messageValues createdResMsgs
    && Logic.checkResourceValues [selfObj.toObjectValue] createdResObjs
    && Logic.checkResourcesPersistent consumedResObjs
    && Logic.checkResourcesEphemeral createdResObjs
    && destructor.invariant selfObj argsData signatures

private def Method.Message.logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  check h : msg.id == .classMember (Label.MemberId.methodId methodId)
  let argsData : methodId.Args.type := cast (by simp! [eq_of_beq h]) msg.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! [selfRes] := consumedResObjs
  let try selfObj : Object classId := Object.fromResource selfRes
  let body := method.body selfObj argsData
  let try vals : body.params.Product := tryCast msg.vals
  let signatures : methodId.Signatures argsData := cast (by grind only) msg.signatures
  check method.invariant selfObj argsData signatures
  let createdObject : Object classId := body |>.value vals
  let messageValues := Program.messageValues body vals
  let createdResMsgs := Logic.selectMessageResources args.created
  Logic.checkMessageResourceValues messageValues createdResMsgs
    && Logic.checkResourceValues [createdObject.toObjectValue] createdResObjs
    && Logic.checkResourcesPersistent consumedResObjs
    && Logic.checkResourcesPersistent createdResObjs

private def Upgrade.Message.logicFun
  {lab : Ecosystem.Label}
  (classId : lab.ClassId)
  (args : Logic.Args)
  : Bool :=
  let! [selfRes] := Logic.selectObjectResources args.consumed
  let! [upgradedRes] := Logic.selectObjectResources args.created
  let try selfObj : Object classId := Object.fromResource selfRes
  let try upgradedObj : SomeObject := SomeObject.fromResource upgradedRes
  selfObj.uid == upgradedObj.object.uid
    && classId.label.isUpgradeable
    && upgradedObj.label == lab
    && upgradedObj.classId.label.name == classId.label.name
    && upgradedObj.classId.label.version > classId.label.version
    && selfRes.isPersistent
    && upgradedRes.isPersistent

/-- The class logic checks if the message consumed in the action is associated
    with the same ecosystem, the `self` object is among the message recipients
    and the number of recipients is equal to the number of consumed object
    resources. The class logic also checks the class invariant for `self`. -/
private def logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (cl : Class classId)
  (args : Logic.Args)
  : Bool :=
  let try self : Object classId := Object.fromResource args.self
  check cl.invariant self args
  match args.status with
  | Created => true
  | Consumed =>
    let consumedObjectResources : List Anoma.Resource := Logic.selectObjectResources args.consumed
    let! [consumedMessageResource] := Logic.selectMessageResources args.consumed
    -- Note: the success of the `try` below ensures that the message is "legal"
    -- for the consumed objects - it is from the same ecosystem
    let try msg : Message lab := Message.fromResource consumedMessageResource
    self.uid ∈ msg.recipients
    && msg.recipients.length == consumedObjectResources.length
    -- Note that the message logics already check if the consumed object
    -- resources have the right form, i.e., correspond to the self / selves. We
    -- only need to check that the number of recipients is equal to the number
    -- of consumed object resources, i.e., there are no extra recipients. The
    -- class logic will be run for each consumed object, with `self` set to that
    -- object, so it will be checked if every consumed object is among the
    -- recipients.

/-- The class logic that is the Resource Logic of each resource corresponding to
  an object of this class. -/
def logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (cl : Class classId)
  : Anoma.Logic :=
  { reference := classId.label.logicRef,
    function := logicFun cl }

def Constructor.Message.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  : Anoma.Logic :=
  { reference := Logic.constructorLogicRef constrId,
    function := Constructor.Message.logicFun constr }

def Destructor.Message.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destrId : classId.label.DestructorId}
  (destr : Class.Destructor classId destrId)
  : Anoma.Logic :=
  { reference := Logic.destructorLogicRef destrId,
    function := Destructor.Message.logicFun destr }

def Method.Message.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  : Anoma.Logic :=
  { reference := Logic.methodLogicRef methodId,
    function := Method.Message.logicFun method }

def Upgrade.Message.logic
  {lab : Ecosystem.Label}
  (classId : lab.ClassId)
  : Anoma.Logic :=
  { reference := Logic.upgradeLogicRef classId,
    function := Upgrade.Message.logicFun classId }

end AVM.Class

namespace AVM.Ecosystem

def MultiMethod.Message.logicFun
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (method : MultiMethod multiId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  check h : msg.id == .multiMethodId multiId
  let fargs : multiId.Args.type := cast (by simp! [eq_of_beq h]) msg.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let argsConsumedSelves := consumedResObjs.take multiId.numObjectArgs
  let try argsConsumedObjects : multiId.Selves := Label.MultiMethodId.ConsumedToSelves argsConsumedSelves
  let argsConstructedEph := consumedResObjs.drop multiId.numObjectArgs
  let prog := method.body argsConsumedObjects fargs
  let signatures := cast (by grind only) msg.signatures
  check method.invariant argsConsumedObjects fargs signatures
  let try vals : prog.params.Product := tryCast msg.vals
  let res : MultiMethodResult multiId := prog |>.value vals
  let data := res.data
  check argsConsumedSelves.length == multiId.numObjectArgs
  check argsConstructedEph.length == data.numConstructed
  let consumedUid (arg : multiId.ObjectArgNames) : Anoma.ObjectId := argsConsumedObjects arg |>.uid
  let mkObjectValue {classId : lab.ClassId} (arg : multiId.ObjectArgNames) (d : ObjectData classId) : ObjectValue := ⟨consumedUid arg, d⟩
  let reassembled : List ObjectValue := res.assembled.withOldUidList.map (fun x => mkObjectValue x.arg x.objectData)
  let constructedObjects : List ObjectValue :=
    List.zipWithExact
      (fun objData res => objData.toObjectValue res.nonce.value)
      res.constructed
      argsConstructedEph
  let consumedDestroyedObjects : List ObjectValue :=
    multiId.objectArgNamesVec.toList.filterMap
      (fun arg =>
        let argObject := argsConsumedObjects arg
        match res.argDeconstruction arg with
        | .Destroyed => argObject |>.data.toObjectValue argObject.uid
        | .Disassembled => none)
  let try (argsCreated, argsConstructed, argsSelvesDestroyedEph, .unit) :=
    createdResObjs
    |> Logic.filterOutDummy
    |>.splitsExact [reassembled.length, data.numConstructed, data.numSelvesDestroyed]
  let messageValues := Program.messageValues prog vals
  let createdResMsgs := Logic.selectMessageResources args.created
  Logic.checkMessageResourceValues messageValues createdResMsgs
    && Logic.checkResourceValues reassembled argsCreated.toList
    && Logic.checkResourceValues constructedObjects argsConstructed.toList
    && Logic.checkResourceValues constructedObjects argsConstructedEph
    && Logic.checkResourceValues consumedDestroyedObjects argsSelvesDestroyedEph.toList
    && Logic.checkResourcesPersistent argsConsumedSelves
    && Logic.checkResourcesPersistent argsCreated.toList
    && Logic.checkResourcesPersistent argsConstructed.toList
    && Logic.checkResourcesEphemeral argsConstructedEph
    && Logic.checkResourcesEphemeral argsSelvesDestroyedEph.toList

def MultiMethod.Message.logic
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (method : MultiMethod multiId)
  : Anoma.Logic :=
  { reference := Logic.multiMethodLogicRef multiId,
    function args := MultiMethod.Message.logicFun method args }

end AVM.Ecosystem
