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
  let try argsData := SomeType.cast msg.args
  let try vals : (constr.body argsData).params.Product := tryCast msg.vals
  let newObjData := constr.body argsData |>.value vals
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! [newObjRes] := createdResObjs
  let uid : ObjectId := newObjRes.nonce.value
  Logic.checkResourceValues [newObjData.toObjectValue uid] consumedResObjs
    && Logic.checkResourceValues [newObjData.toObjectValue uid] createdResObjs
    && Logic.checkResourcesEphemeral consumedResObjs
    && Logic.checkResourcesPersistent createdResObjs
    && constr.invariant argsData

/-- Creates a message logic function for a given destructor. -/
private def Destructor.Message.logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor classId destructorId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  let try argsData := SomeType.cast msg.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! [selfRes] := consumedResObjs
  let try selfObj : Object classId := Object.fromResource selfRes
  Logic.checkResourceValues [selfObj.toObjectValue] createdResObjs
    && Logic.checkResourcesPersistent consumedResObjs
    && Logic.checkResourcesEphemeral createdResObjs
    && destructor.invariant selfObj argsData

/-- Creates a message logic function for a given method. -/
private def Method.Message.logicFun
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method classId methodId)
  (args : Logic.Args)
  : Bool :=
  let try msg : Message lab := Message.fromResource args.self
  let try argsData := SomeType.cast msg.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let! [selfRes] := consumedResObjs
  let try selfObj : Object classId := Object.fromResource selfRes
  check method.invariant selfObj argsData
  let body := method.body selfObj argsData
  let try vals : body.params.Product := tryCast msg.vals
  let createdObject : Object classId := body |>.value vals
  Logic.checkResourceValues [createdObject.toObjectValue] createdResObjs
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
    let try msg : Message lab := Message.fromResource consumedMessageResource
    -- Note: the success of the `try` below ensures that the message is "legal"
    -- for the consumed objects - it is from the same ecosystem
    let recipients := msg.recipients.toList
    self.uid ∈ recipients
    && recipients.length == consumedObjectResources.length
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
  let try fargs : multiId.Args.type := SomeType.cast msg.args
  let consumedResObjs := Logic.selectObjectResources args.consumed
  let createdResObjs := Logic.selectObjectResources args.created
  let try (argsConsumedSelves, argsConstructedEph, .unit) :=
      consumedResObjs
      |> Logic.filterOutDummy
      |>.splitsExact [multiId.numObjectArgs, data.numConstructed]
  let try argsConsumedObjects : multiId.Selves := Label.MultiMethodId.ConsumedToSelves argsConsumedSelves.toList
  let prog := method.body argsConsumedObjects fargs
  method.invariant argsConsumedObjects fargs
   && let try vals : prog.params.Product := tryCast msg.vals
      let res : MultiMethodResult multiId := prog |>.value vals
      let consumedUid (arg : multiId.ObjectArgNames) : Anoma.ObjectId := argsConsumedObjects arg |>.uid
      let mkObjectValue {classId : lab.ClassId} (arg : multiId.ObjectArgNames) (d : ObjectData classId) : ObjectValue := ⟨consumedUid arg, d⟩
      let reassembled : List ObjectValue := res.assembled.withOldUidList.map (fun x => mkObjectValue x.arg x.objectData)
      let constructedObjects : List ObjectValue := res.constructed
      let consumedDestroyedObjects : List ObjectValue :=
        multiId.objectArgNamesVec.toList.filterMap (fun arg =>
        let argObject := argsConsumedObjects arg
        match res.argDeconstruction arg with
        | .Destroyed => argObject |>.data.toObjectValue argObject.uid
        | .Disassembled => none)
      let try (argsCreated, argsConstructed, argsSelvesDestroyedEph, .unit) :=
        createdResObjs
        |> Logic.filterOutDummy
        |>.splitsExact [reassembled.length, data.numConstructed, data.numSelvesDestroyed]
      Logic.checkResourceValues reassembled argsCreated.toList
        && Logic.checkResourceValues constructedObjects argsConstructed.toList
        && Logic.checkResourceValues constructedObjects argsConstructedEph.toList
        && Logic.checkResourceValues consumedDestroyedObjects argsSelvesDestroyedEph.toList
        && Logic.checkResourcesPersistent argsConsumedSelves.toList
        && Logic.checkResourcesPersistent argsCreated.toList
        && Logic.checkResourcesPersistent argsConstructed.toList
        && Logic.checkResourcesEphemeral argsConstructedEph.toList
        && Logic.checkResourcesEphemeral argsSelvesDestroyedEph.toList

def MultiMethod.Message.logic
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (method : MultiMethod multiId)
  (data : MultiMethodData)
  : Anoma.Logic :=
  { reference := ⟨s!"AVM.MultiMethod.{@repr _ lab.multiMethodsRepr multiId}"⟩,
    function args := MultiMethod.Message.logicFun method args data }

end AVM.Ecosystem
