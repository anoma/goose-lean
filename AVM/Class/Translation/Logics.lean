import AVM.Class
import AVM.Message
import AVM.Logic
import AVM.Ecosystem

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
  | .log _ next => messageValues next vals

end AVM.Program

namespace AVM.Logic

def checkMessageResourceValues {lab : Ecosystem.Label} (vals : List (Program.MessageValue lab)) (resMsgs : List Anoma.Resource) : Bool :=
  vals.length == resMsgs.length &&
  List.all₂
    (fun val res =>
      let try msg : Message lab := Message.fromResource res
      msg.data.id == val.id && msg.data.args === val.args)
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
  : Anoma.LogicM := do
  docheck h : msg.data.id == .multiMethodId multiId
  let fargs : multiId.Args.type := cast (by simp! [eq_of_beq h]) msg.data.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let argsConsumedSelves := consumedResObjs.take multiId.numObjectArgs
  do
  let catch argsConsumedObjects : multiId.Selves := Label.MultiMethodId.ConsumedToSelves argsConsumedSelves
    failwith fun err => throw (.custom here# err)
  docheck method.invariant msg argsConsumedObjects fargs
  let prog := method.body argsConsumedObjects fargs
  let try vals : prog.params.Product := tryCast msg.data.vals
  let res : MultiMethodResult multiId := prog.value vals
  let valsObjs := prog.objects vals
  let fetchedObjValues := valsObjs.map (·.toObjectValue)
  let data := res.data
  docheck argsConsumedSelves.length == multiId.numObjectArgs
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
  docheck Logic.checkMessageResourceValues messageValues createdResMsgs
  Logic.checkResourceValues reassembled argsCreated.toList
  Logic.checkResourceValues constructedObjects argsConstructed.toList
  Logic.checkResourceValues constructedObjects argsConstructedEph.toList
  Logic.checkResourceValues consumedDestroyedObjects argsSelvesDestroyedEph.toList
  Logic.checkResourceValues fetchedObjValues consumedFetchedResObjs.toList
  Logic.checkResourceValues fetchedObjValues createdFetchedResObjs.toList
  docheck Logic.checkResourcesPersistent argsConsumedSelves
    && Logic.checkResourcesPersistent argsCreated.toList
    && Logic.checkResourcesPersistent argsConstructed.toList
    && Logic.checkResourcesPersistent consumedFetchedResObjs.toList
    && Logic.checkResourcesPersistent createdFetchedResObjs.toList
    && Logic.checkResourcesEphemeral argsConstructedEph.toList
    && Logic.checkResourcesEphemeral argsSelvesDestroyedEph.toList
  Anoma.LogicM.true

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
  : Anoma.LogicM := Anoma.LogicM.withTrace here# "Constructor.Message.logicFun" do
  docheck h : msg.data.id == .classMember (Label.MemberId.constructorId constrId)
  let argsData : constrId.Args.type := cast (by simp! [eq_of_beq h]) msg.data.args
  let body := constr.body argsData
  let try vals : body.params.Product := tryCast msg.data.vals
  let newObjData := body.value vals
  let consumedResObjs := Logic.selectObjectResources (args.consumed ++ if args.isConsumed then [args.self] else [])
  let createdResObjs := Logic.selectObjectResources (args.created ++ if args.isConsumed then [] else [args.self])
  dolet! (newObjRes :: _) := createdResObjs
  dolet! (consumedObjRes :: consumedFetchedResObjs) := consumedResObjs
    failwith throw (.custom here#
    s!"consumedResObjs.length = {consumedResObjs.length}
    args.consumed:\n{repr args.consumed}
    args.created:\n{repr args.created}
    self:\n{repr args.self}
    self.isConsumed: {repr args.isConsumed}")
  let uid : ObjectId := newObjRes.nonce.value
  let messageValues := Program.messageValues body vals
  let createdResMsgs := Logic.selectMessageResources (args.created  ++ if args.isConsumed then [] else [args.self])
  let valsObjs := body.objects vals
  let fetchedObjValues := valsObjs.map (·.toObjectValue)
  let newObjValue := newObjData.toObjectValue uid
  docheck Logic.checkMessageResourceValues messageValues createdResMsgs
  Logic.checkResourceValues (newObjValue :: fetchedObjValues) consumedResObjs
  Logic.checkResourceValues (newObjValue :: fetchedObjValues) createdResObjs
  docheck Logic.checkResourcesEphemeral [consumedObjRes]
  docheck Logic.checkResourcesPersistent createdResObjs
  docheck Logic.checkResourcesPersistent consumedFetchedResObjs
  docheck constr.invariant msg argsData
  Anoma.LogicM.true

/-- Creates a message logic function for a given destructor. -/
private def Destructor.Message.logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor classId destructorId)
  (msg : Message lab)
  (args : Logic.Args)
  : Anoma.LogicM := do
  docheck h : msg.data.id == .classMember (Label.MemberId.destructorId destructorId)
  let argsData := cast (by simp! [eq_of_beq h]) msg.data.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  dolet! (selfRes :: _) := consumedResObjs
  dolet! (createdResObj :: createdFetchedResObjs) := createdResObjs
  let catch selfObj : Object classId := Object.fromResource selfRes
    failwith fun (err : String) => throw (.custom here# err)
  let body := destructor.body selfObj argsData
  let try vals : body.params.Product := tryCast msg.data.vals
  let messageValues := Program.messageValues body vals
  let createdResMsgs := Logic.selectMessageResources args.created
  let valsObjs := body.objects vals
  let fetchedObjValues := valsObjs.map (·.toObjectValue)
  let selfObjValue := selfObj.toObjectValue
  docheck Logic.checkMessageResourceValues messageValues createdResMsgs
  Logic.checkResourceValues (selfObjValue :: fetchedObjValues) createdResObjs
  Logic.checkResourceValues (selfObjValue :: fetchedObjValues) consumedResObjs
  docheck Logic.checkResourcesPersistent consumedResObjs
    && Logic.checkResourcesEphemeral [createdResObj]
    && Logic.checkResourcesPersistent createdFetchedResObjs
    && destructor.invariant msg selfObj argsData
  Anoma.LogicM.true

private def Method.Message.logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (msg : Message lab)
  (args : Logic.Args)
  : Anoma.LogicM := do
  docheck h : msg.data.id == .classMember (Label.MemberId.methodId methodId)
  let argsData : methodId.Args.type := cast (by simp! [eq_of_beq h]) msg.data.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! (selfRes :: _) := consumedResObjs
  let catch selfObj : Object classId := Object.fromResource selfRes
    failwith fun err => throw (.custom here# err)
  let body := method.body selfObj argsData
  let try vals : body.params.Product := tryCast msg.data.vals
  do -- TODO fix
  docheck method.invariant msg selfObj argsData
  let createdObject : Object classId := body |>.value vals
  let messageValues := Program.messageValues body vals
  let createdResMsgs := Logic.selectMessageResources args.created
  let valsObjs := body.objects vals
  let fetchedObjValues := valsObjs.map (·.toObjectValue)
  docheck Logic.checkMessageResourceValues messageValues createdResMsgs
  Logic.checkResourceValues (createdObject.toObjectValue :: fetchedObjValues) createdResObjs
  Logic.checkResourceValues (selfObj.toObjectValue :: fetchedObjValues) consumedResObjs
  docheck Logic.checkResourcesPersistent consumedResObjs
    && Logic.checkResourcesPersistent createdResObjs
  Anoma.LogicM.true

private def Upgrade.Message.logicFun
  {lab : Ecosystem.Label}
  (classId : lab.ClassId)
  (args : Logic.Args)
  : Anoma.LogicM :=
  let! [selfRes] := Logic.selectObjectResources args.consumed
  let! [upgradedRes] := Logic.selectObjectResources args.created
  let catch selfObj : Object classId := Object.fromResource selfRes
    failwith fun err => throw (.custom here# err)
  let catch upgradedObj : SomeObject := SomeObject.fromResource upgradedRes
    failwith fun err => throw (.custom here# err)
  check selfObj.uid == upgradedObj.object.uid
    && classId.label.isUpgradeable
    && upgradedObj.label == lab
    && upgradedObj.classId.label.name == classId.label.name
    && upgradedObj.classId.label.version > classId.label.version
    && selfRes.isPersistent
    && upgradedRes.isPersistent
  .true

private def Member.logicFun
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (member : lab.MemberId)
  (msg : Message lab)
  (args : Logic.Args)
  : Anoma.LogicM :=
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
  (eco : Ecosystem lab)
  (classId : lab.ClassId)
  (args : Logic.Args)
  : Anoma.LogicM :=
  let catch self : Object classId := Object.fromResource args.self
    failwith fun err => throw (.custom here# s!"Failed to decode self to an Object:
    error: {err}
    ------
    Resource:
    {repr args.self}")
  check eco.classes classId |>.invariant self args
  match args.status with
  | Created => .true
  | Consumed =>
    if args.self.isPersistent && Logic.isObjectPreserved self.toObjectValue args.created then
      .true
    else
      let! [consumedMessageResource] := Logic.selectMessageResources args.consumed
      -- Note: the success of the `try` below ensures that the message is "legal"
      -- for the consumed objects - it is from the same ecosystem
      let try msg : Message lab := Message.fromResource consumedMessageResource
      check self.uid ∈ msg.data.recipients
      Member.logicFun eco msg.data.id msg args

/-- The class logic that is the Resource Logic of each resource corresponding to
  an object of this class. -/
def logic
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (classId : lab.ClassId)
  : Anoma.Logic :=
  { reference := classId.label.logicRef,
    function := logicFun eco classId }

end AVM.Class
