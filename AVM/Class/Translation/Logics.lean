import AVM.Class
import AVM.Message
import AVM.Logic
import AVM.Ecosystem

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
  match msg with
  | {id := id, contents := contents} =>
  -- TODO check syntax
  if h : id == .classMember (Label.MemberId.constructorId constrId)
  then
    let contents : MessageContents lab (.classMember (Label.MemberId.constructorId constrId)) := eq_of_beq h ▸ contents
    let argsData := contents.args
    let try vals : (constr.body argsData).params.Product := tryCast contents.vals
    let newObjData := constr.body argsData |>.value vals
    let consumedResObjs := Logic.selectObjectResources args.consumed
    let createdResObjs := Logic.selectObjectResources args.created
    let signatures := contents.signatures
    let! [newObjRes] := createdResObjs
    let uid : ObjectId := newObjRes.nonce.value
    Logic.checkResourceValues [newObjData.toObjectValue uid] consumedResObjs
      && Logic.checkResourceValues [newObjData.toObjectValue uid] createdResObjs
      && Logic.checkResourcesEphemeral consumedResObjs
      && Logic.checkResourcesPersistent createdResObjs
      && constr.invariant argsData signatures
  else false

/-- Creates a message logic function for a given destructor. -/
private def Destructor.Message.logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor classId destructorId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  match msg with
  | {id := id, contents := contents} =>
  -- TODO check syntax
  if h : id == .classMember (Label.MemberId.destructorId destructorId)
  then
    let contents : MessageContents lab (.classMember (Label.MemberId.destructorId destructorId)) := eq_of_beq h ▸ contents
    let argsData := contents.args
    let signatures : destructorId.Signatures argsData := contents.signatures
    let consumedResObjs := Logic.selectObjectResources args.consumed
    let createdResObjs := Logic.selectObjectResources args.created
    let! [selfRes] := consumedResObjs
    let try selfObj : Object classId := Object.fromResource selfRes
    Logic.checkResourceValues [selfObj.toObjectValue] createdResObjs
      && Logic.checkResourcesPersistent consumedResObjs
      && Logic.checkResourcesEphemeral createdResObjs
      && destructor.invariant selfObj argsData signatures
  else false

private def Method.Message.logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  match msg with
  | {id := id, contents := contents} =>
  if h : id == .classMember (Label.MemberId.methodId methodId)
  then
    let contents : MessageContents lab (.classMember (Label.MemberId.methodId methodId)) := eq_of_beq h ▸ contents
    let argsData : methodId.Args.type := contents.args
    let consumedResObjs := Logic.selectObjectResources args.consumed
    let createdResObjs := Logic.selectObjectResources args.created
    let! [selfRes] := consumedResObjs
    let try selfObj : Object classId := Object.fromResource selfRes
    let body := method.body selfObj argsData
    let try vals : body.params.Product := tryCast contents.vals
    let signatures : methodId.Signatures argsData := contents.signatures
    check method.invariant selfObj argsData signatures
    let createdObject : Object classId := body |>.value vals
    Logic.checkResourceValues [createdObject.toObjectValue] createdResObjs
      && Logic.checkResourcesPersistent consumedResObjs
      && Logic.checkResourcesPersistent createdResObjs
  else false

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

/-- The class logic checks if all consumed messages in the action correspond to
    class members, the single consumed object is the receiver, and there is
    at least one message. -/
private def logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (cl : Class classId)
  (consumedMessageResources consumedObjectResources : List Anoma.Resource)
  (args : Logic.Args)
  : Bool :=
  let try self : Object classId := Object.fromResource args.self
  check cl.invariant self args
  match args.status with
  | Created => true
  | Consumed =>
    let nMessages := consumedMessageResources.length
    let! [consumedObjectResource] : List Anoma.Resource := consumedObjectResources
    let try consumedObject : Object classId := Object.fromResource consumedObjectResource
    -- NOTE: consumedObject == self by definition of Logic.Args; we only check
    -- that there are no other consumed objects
    nMessages + 1 == (Logic.filterOutDummy args.consumed).length
      && consumedMessageResources.all fun res =>
        let try msg : Message lab := Message.fromResource res
        let! [recipient] := msg.contents.recipients.toList
        consumedObject.uid == recipient

def Constructor.Message.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor classId constrId)
  : Anoma.Logic :=
  { reference := ⟨s!"AVM.Class.{classId.label.name}.Constructor.{@repr _ classId.label.constructorsRepr constrId}"⟩,
    function := Constructor.Message.logicFun constr }

def Destructor.Message.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destrId : classId.label.DestructorId}
  (destr : Class.Destructor classId destrId)
  : Anoma.Logic :=
  { reference := ⟨s!"AVM.Class.{classId.label.name}.Destructor.{@repr _ classId.label.destructorsRepr destrId}"⟩,
    function := Destructor.Message.logicFun destr }

def Method.Message.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  : Anoma.Logic :=
  { reference := ⟨s!"AVM.Class.{classId.label.name}.Method.{@repr _ classId.label.methodsRepr methodId}"⟩,
    function := Method.Message.logicFun method }

def Upgrade.Message.logic
  {lab : Ecosystem.Label}
  (classId : lab.ClassId)
  : Anoma.Logic :=
  { reference := ⟨s!"AVM.Class.{classId.label.name}.Upgrade"⟩,
    function := Upgrade.Message.logicFun classId }

end AVM.Class

namespace AVM.Ecosystem

def MultiMethod.Message.logicFun
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (method : MultiMethod multiId)
  (args : Logic.Args)
  (data : MultiMethodData)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  match msg with
  | {id := id, contents := contents} =>
  if h : id == .multiMethodId multiId
  then
    let contents : MessageContents lab (.multiMethodId multiId) := eq_of_beq h ▸ contents
    let fargs : multiId.Args.type := contents.args
    let consumedResObjs := Logic.selectObjectResources args.consumed
    let createdResObjs := Logic.selectObjectResources args.created
    let try (argsConsumedSelves, argsConstructedEph, argsDestroyed, .unit) :=
        consumedResObjs
        |> Logic.filterOutDummy
        |>.splitsExact [multiId.numObjectArgs, data.numConstructed, data.numDestroyed]
    let try argsConsumedObjects : multiId.Selves := Label.MultiMethodId.ConsumedToSelves argsConsumedSelves.toList
    let prog := method.body argsConsumedObjects fargs
    method.invariant argsConsumedObjects fargs contents.signatures
     && let try vals : prog.params.Product := tryCast msg.contents.vals
        let res : MultiMethodResult multiId := prog |>.value vals
        let consumedUid (arg : multiId.ObjectArgNames) : Anoma.ObjectId := argsConsumedObjects arg |>.uid
        let mkObjectValue {classId : lab.ClassId} (arg : multiId.ObjectArgNames) (d : ObjectData classId) : ObjectValue := ⟨consumedUid arg, d⟩
        let reassembled : List ObjectValue := res.assembled.withOldUidList.map (fun x => mkObjectValue x.arg x.objectData)
        let destroyedObjects : List ObjectValue := res.destroyed.map (fun x => x.toSomeObject.toObjectValue)
        let constructedObjects : List ObjectValue := res.constructed
        let consumedDestroyedObjects : List ObjectValue :=
          multiId.objectArgNamesVec.toList.filterMap (fun arg =>
          let argObject := argsConsumedObjects arg
          match res.argDeconstruction arg with
          | .Destroyed => argObject |>.data.toObjectValue argObject.uid
          | .Disassembled => none)
        let try (argsCreated, argsConstructed, argsDestroyedEph, argsSelvesDestroyedEph, .unit) :=
          createdResObjs
          |> Logic.filterOutDummy
          |>.splitsExact [reassembled.length, data.numConstructed, data.numDestroyed, data.numSelvesDestroyed]
        Logic.checkResourceValues reassembled argsCreated.toList
          && Logic.checkResourceValues destroyedObjects argsDestroyed.toList
          && Logic.checkResourceValues destroyedObjects argsDestroyedEph.toList
          && Logic.checkResourceValues constructedObjects argsConstructed.toList
          && Logic.checkResourceValues constructedObjects argsConstructedEph.toList
          && Logic.checkResourceValues consumedDestroyedObjects argsSelvesDestroyedEph.toList
          && Logic.checkResourcesPersistent argsConsumedSelves.toList
          && Logic.checkResourcesPersistent argsDestroyed.toList
          && Logic.checkResourcesPersistent argsCreated.toList
          && Logic.checkResourcesPersistent argsConstructed.toList
          && Logic.checkResourcesEphemeral argsConstructedEph.toList
          && Logic.checkResourcesEphemeral argsDestroyedEph.toList
          && Logic.checkResourcesEphemeral argsSelvesDestroyedEph.toList
  else false

def MultiMethod.Message.logic
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (method : MultiMethod multiId)
  (data : MultiMethodData)
  : Anoma.Logic :=
  { reference := ⟨s!"AVM.MultiMethod.{@repr _ lab.multiMethodsRepr multiId}"⟩,
    function args := MultiMethod.Message.logicFun method args data }

/-- The multiMethod logic checks that all consumed messages in the action correspond
  to members in the ecosystem and the consumed objects are the receivers. -/
private def logicFun
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Logic.Args)
  : Bool :=
  match args.status with
  | Created => true
  | Consumed =>
      let consumedMessageResources : List Anoma.Resource := Logic.selectMessageResources args.consumed
      let nMessages := consumedMessageResources.length
      let consumedObjectResources : List Anoma.Resource := Logic.selectObjectResources args.consumed
      nMessages >= 1
        && consumedMessageResources.all fun res =>
          let try msg : Message lab := Message.fromResource res
          match msg.id with
          | .classMember (classId := cl) _ => AVM.Class.logicFun (eco.classes cl) consumedMessageResources consumedObjectResources args
          | .multiMethodId multiId =>
            let try selves : multiId.Selves := multiId.ConsumedToSelves consumedObjectResources
            nMessages + multiId.numObjectArgs == (Logic.filterOutDummy args.consumed).length
              && Label.MultiMethodId.SelvesToVector selves (fun o => o.uid) ≍? msg.contents.recipients

def logic
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  : Anoma.Logic :=
  { reference := lab.logicRef,
    function := logicFun eco }
