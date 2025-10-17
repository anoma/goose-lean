import AVM.Class
import AVM.Message
import AVM.Logic
import AVM.Ecosystem

namespace AVM.Logic

def classLogicRef {lab : Ecosystem.Label} (classId : lab.ClassId) : Anoma.LogicRef :=
  classId.label.logicRef

def trivialLogicRef : Anoma.LogicRef := Anoma.LogicRef.mk "Anoma.TrivialLogic"

def trivialLogic : Anoma.Logic :=
  { reference := trivialLogicRef,
    function := fun _ => true }

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
        logicRef := Logic.trivialLogicRef }
    let ⟨objId, vals'⟩ := vals
    msgData :: Program.messageValues (next objId) vals'
  | .destructor _ _ destrId _ args _ next =>
    let msgData : MessageValue lab :=
      { id := .classMember (.destructorId destrId)
        args := args,
        logicRef := Logic.trivialLogicRef }
    msgData :: Program.messageValues next vals
  | .method _ _ methodId _ args _ next =>
    let msgData : MessageValue lab :=
      { id := .classMember (.methodId methodId)
        args := args,
        logicRef := Logic.trivialLogicRef }
    msgData :: Program.messageValues next vals
  | .multiMethod _ mid _ args _ next =>
    let msgData : MessageValue lab :=
      { id := .multiMethodId mid
        args := args,
        logicRef := Logic.trivialLogicRef }
    msgData :: Program.messageValues next vals
  | .upgrade _ cid _ _ next =>
    let msgData : MessageValue lab :=
      { id := .classMember (classId := cid) .upgradeId
        args := PUnit.unit,
        logicRef := Logic.trivialLogicRef }
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

namespace AVM.Ecosystem

def MultiMethod.Message.logicFun
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (method : MultiMethod multiId)
  (msg : Message lab)
  (args : Logic.Args)
  : Bool :=
  check h : msg.id == .multiMethodId multiId
  let fargs : multiId.Args.type := cast (by simp! [eq_of_beq h]) msg.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let argsConsumedSelves := consumedResObjs.take multiId.numObjectArgs
  let try argsConsumedObjects : multiId.Selves := Label.MultiMethodId.ConsumedToSelves argsConsumedSelves
  let prog := method.body argsConsumedObjects fargs
  let signatures := cast (by grind only) msg.signatures
  check method.invariant argsConsumedObjects fargs signatures
  let try vals : prog.params.Product := tryCast msg.vals
  let res : MultiMethodResult multiId := prog.value vals
  let valsObjs := prog.objects vals
  let fetchedObjValues := valsObjs.map (·.toObjectValue)
  let data := res.data
  check argsConsumedSelves.length == multiId.numObjectArgs
  let try (argsConstructedEph, consumedFetchedResObjs, .unit) :=
    consumedResObjs.drop multiId.numObjectArgs
    |>.splitsExact [data.numConstructed, valsObjs.length]
  let consumedUid (arg : multiId.ObjectArgNames) : Anoma.ObjectId := argsConsumedObjects arg |>.uid
  let mkObjectValue {classId : lab.ClassId} (arg : multiId.ObjectArgNames) (d : ObjectData classId) : ObjectValue := ⟨consumedUid arg, d⟩
  let reassembled : List ObjectValue := res.assembled.withOldUidList.map (fun x => mkObjectValue x.arg x.objectData)
  let constructedObjects : List ObjectValue :=
    List.zipWithExact
      (fun objData res => objData.toObjectValue res.nonce.value)
      res.constructed
      argsConstructedEph.toList
  let consumedDestroyedObjects : List ObjectValue :=
    multiId.objectArgNamesVec.toList.filterMap
      (fun arg =>
        let argObject := argsConsumedObjects arg
        match res.argDeconstruction arg with
        | .Destroyed => argObject |>.data.toObjectValue argObject.uid
        | .Disassembled => none)
  let try (argsCreated, argsConstructed, argsSelvesDestroyedEph, createdFetchedResObjs, .unit) :=
    createdResObjs
    |> Logic.filterOutDummy
    |>.splitsExact [reassembled.length, data.numConstructed, data.numSelvesDestroyed, valsObjs.length]
  let messageValues := Program.messageValues prog vals
  let createdResMsgs := Logic.selectMessageResources args.created
  Logic.checkMessageResourceValues messageValues createdResMsgs
    && Logic.checkResourceValues reassembled argsCreated.toList
    && Logic.checkResourceValues constructedObjects argsConstructed.toList
    && Logic.checkResourceValues constructedObjects argsConstructedEph.toList
    && Logic.checkResourceValues consumedDestroyedObjects argsSelvesDestroyedEph.toList
    && Logic.checkResourceValues fetchedObjValues consumedFetchedResObjs.toList
    && Logic.checkResourceValues fetchedObjValues createdFetchedResObjs.toList
    && Logic.checkResourcesPersistent argsConsumedSelves
    && Logic.checkResourcesPersistent argsCreated.toList
    && Logic.checkResourcesPersistent argsConstructed.toList
    && Logic.checkResourcesPersistent consumedFetchedResObjs.toList
    && Logic.checkResourcesPersistent createdFetchedResObjs.toList
    && Logic.checkResourcesEphemeral argsConstructedEph.toList
    && Logic.checkResourcesEphemeral argsSelvesDestroyedEph.toList

end AVM.Ecosystem

namespace AVM.Class

/-- Creates a message logic function for a given constructor. -/
private def Constructor.Message.logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  (msg : Message lab)
  (args : Logic.Args)
  : Bool :=
  check h : msg.id == .classMember (Label.MemberId.constructorId constrId)
  let argsData : constrId.Args.type := cast (by simp! [eq_of_beq h]) msg.args
  let signatures : constrId.Signatures argsData := cast (by grind only) msg.signatures
  let body := constr.body argsData
  let try vals : body.params.Product := tryCast msg.vals
  let newObjData := body.value vals
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! (newObjRes :: _) := createdResObjs
  let! (consumedObjRes :: consumedFetchedResObjs) := consumedResObjs
  let uid : ObjectId := newObjRes.nonce.value
  let messageValues := Program.messageValues body vals
  let createdResMsgs := Logic.selectMessageResources args.created
  let valsObjs := body.objects vals
  let fetchedObjValues := valsObjs.map (·.toObjectValue)
  let newObjValue := newObjData.toObjectValue uid
  Logic.checkMessageResourceValues messageValues createdResMsgs
    && Logic.checkResourceValues (newObjValue :: fetchedObjValues) consumedResObjs
    && Logic.checkResourceValues (newObjValue :: fetchedObjValues) createdResObjs
    && Logic.checkResourcesEphemeral [consumedObjRes]
    && Logic.checkResourcesPersistent createdResObjs
    && Logic.checkResourcesPersistent consumedFetchedResObjs
    && constr.invariant argsData signatures

/-- Creates a message logic function for a given destructor. -/
private def Destructor.Message.logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor classId destructorId)
  (msg : Message lab)
  (args : Logic.Args)
  : Bool :=
  check h : msg.id == .classMember (Label.MemberId.destructorId destructorId)
  let argsData := cast (by simp! [eq_of_beq h]) msg.args
  let signatures : destructorId.Signatures argsData := cast (by grind only) msg.signatures
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! (selfRes :: _) := consumedResObjs
  let! (createdResObj :: createdFetchedResObjs) := createdResObjs
  let try selfObj : Object classId := Object.fromResource selfRes
  let body := destructor.body selfObj argsData
  let try vals : body.params.Product := tryCast msg.vals
  let messageValues := Program.messageValues body vals
  let createdResMsgs := Logic.selectMessageResources args.created
  let valsObjs := body.objects vals
  let fetchedObjValues := valsObjs.map (·.toObjectValue)
  let selfObjValue := selfObj.toObjectValue
  Logic.checkMessageResourceValues messageValues createdResMsgs
    && Logic.checkResourceValues (selfObjValue :: fetchedObjValues) createdResObjs
    && Logic.checkResourceValues (selfObjValue :: fetchedObjValues) consumedResObjs
    && Logic.checkResourcesPersistent consumedResObjs
    && Logic.checkResourcesEphemeral [createdResObj]
    && Logic.checkResourcesPersistent createdFetchedResObjs
    && destructor.invariant selfObj argsData signatures

private def Method.Message.logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (msg : Message lab)
  (args : Logic.Args)
  : Bool :=
  check h : msg.id == .classMember (Label.MemberId.methodId methodId)
  let argsData : methodId.Args.type := cast (by simp! [eq_of_beq h]) msg.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! (selfRes :: _) := consumedResObjs
  let try selfObj : Object classId := Object.fromResource selfRes
  let body := method.body selfObj argsData
  let try vals : body.params.Product := tryCast msg.vals
  let signatures : methodId.Signatures argsData := cast (by grind only) msg.signatures
  check method.invariant selfObj argsData signatures
  let createdObject : Object classId := body |>.value vals
  let messageValues := Program.messageValues body vals
  let createdResMsgs := Logic.selectMessageResources args.created
  let valsObjs := body.objects vals
  let fetchedObjValues := valsObjs.map (·.toObjectValue)
  Logic.checkMessageResourceValues messageValues createdResMsgs
    && Logic.checkResourceValues (createdObject.toObjectValue :: fetchedObjValues) createdResObjs
    && Logic.checkResourceValues (selfObj.toObjectValue :: fetchedObjValues) consumedResObjs
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

private def Member.logicFun
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (member : lab.MemberId)
  (msg : Message lab)
  (args : Logic.Args)
  : Bool :=
  match member with
  | .multiMethodId multiId =>
    let method : Ecosystem.MultiMethod multiId := eco.multiMethods multiId
    Ecosystem.MultiMethod.Message.logicFun method msg args
  | .classMember (classId := classId) memId =>
    let cl := eco.classes classId
    match memId with
    | .constructorId constrId =>
      let constr := cl.constructors constrId
      Constructor.Message.logicFun constr msg args
    | .destructorId destrId =>
      let destr := cl.destructors destrId
      Destructor.Message.logicFun destr msg args
    | .methodId methodId =>
      let method := cl.methods methodId
      Method.Message.logicFun method msg args
    | .upgradeId =>
      Upgrade.Message.logicFun classId args

/--
  The class logic checks if one the following holds.
  1. The `self` object is preserved (not modified).
  2. The `self` object is a recipient of the message and the consumed message
     logic holds.

  The class logic also checks the class invariant for `self`.
  -/
private def logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (eco : Ecosystem lab)
  (cl : Class classId)
  (args : Logic.Args)
  : Bool :=
  let try self : Object classId := Object.fromResource args.self
  check cl.invariant self args
  match args.status with
  | Created => true
  | Consumed =>
    if args.self.isPersistent && Logic.isObjectPreserved self.toObjectValue args.created then
      true
    else
      let! [consumedMessageResource] := Logic.selectMessageResources args.consumed
      -- Note: the success of the `try` below ensures that the message is "legal"
      -- for the consumed objects - it is from the same ecosystem
      let try msg : Message lab := Message.fromResource consumedMessageResource
      self.uid ∈ msg.recipients
      && Member.logicFun eco msg.id msg args

/-- The class logic that is the Resource Logic of each resource corresponding to
  an object of this class. -/
def logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (eco : Ecosystem lab)
  (cl : Class classId)
  : Anoma.Logic :=
  { reference := classId.label.logicRef,
    function := logicFun eco cl }

end AVM.Class
