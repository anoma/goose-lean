
import Mathlib.Control.Random
import Prelude
import Anoma
import AVM.Class
import AVM.Object
import AVM.Object.Consumable
import AVM.Class.Member
import AVM.Class.Member.Logic

namespace AVM.Class

private structure CreatedObject where
  {label : Label}
  object : Object label
  resource : Anoma.Resource
  commitment : Anoma.Commitment

/-- Helper function to create an Action. Handles the random number generator
  explicitly (needed to avoid universe level inconsistencies with monadic
  notation). -/
private def Action.create' (g : StdGen) (lab : Label) (memberId : Label.MemberId lab)
  (args : memberId.Args.type)
  (consumed : ConsumedObject lab)
  (created : List CreatedObject) -- no appdata/logic
  : Anoma.Action × StdGen :=
  let createdResources : List Anoma.Resource := created.map CreatedObject.resource
  let (createdUnits, g') : List Anoma.ComplianceUnit × StdGen :=
    createdResources.foldr mkCreatedComplianceUnit ([], g)
  let logicVerifierInputs : Std.HashMap Anoma.Tag Anoma.LogicVerifierInput :=
    Std.HashMap.emptyWithCapacity
    |>.insertMany [Prod.map id (mkLogicVerifierInput Consumed) (mkTagDataPairConsumed consumed)]
    |>.insertMany (List.map (Prod.map id (mkLogicVerifierInput Created) ∘ mkTagDataPairCreated) created)
  let consumedResource : Anoma.Resource := consumed.resource
  let consumedUnit : Anoma.ComplianceUnit :=
    Anoma.ComplianceUnit.create
      { consumedResource := consumedResource
        createdResource := dummyResource consumed.can_nullify.nullifier.toNonce
        nfKey := consumed.key }
  let action : Anoma.Action :=
    { complianceUnits := consumedUnit :: createdUnits,
      logicVerifierInputs }
  (action, g')
  where
    mkCreatedComplianceUnit  (res : Anoma.Resource) : List Anoma.ComplianceUnit × StdGen → List Anoma.ComplianceUnit × StdGen
      | (acc, g) =>
        let (r, g') := stdNext g
        let complianceUnit :=
          Anoma.ComplianceUnit.create
            { consumedResource := dummyResource r
              createdResource := res
              nfKey := Anoma.NullifierKey.universal }
        (complianceUnit :: acc, g')

    mkLogicVerifierInput (status : ConsumedCreated) (data : Class.SomeAppData) : Anoma.LogicVerifierInput :=
      { Data := ⟨Class.SomeAppData⟩,
        status,
        appData := data }

    mkTagDataPairConsumed (i : ConsumedObject lab)
     : Anoma.Tag × Class.SomeAppData :=
      (Anoma.Tag.Consumed i.can_nullify.nullifier,
        { appData := {
            memberId,
            memberArgs := args }})

    mkTagDataPairCreated (i : CreatedObject)
     : Anoma.Tag × Class.SomeAppData :=
      (Anoma.Tag.Created i.commitment,
        {label := i.label,
         appData := {
          memberId := Label.MemberId.falseLogicId,
          memberArgs := UUnit.unit }})

/-- Helper function to create an Action. -/
private def Action.create (lab : Label) (memberId : Label.MemberId lab)
  (args : memberId.Args.type)
  (consumed : ConsumedObject lab)
  (created : List CreatedObject) -- no appdata/logic
  : Rand Anoma.Action := do
  let g ← get
  let (action, g') := Action.create' g.down lab memberId args consumed created
  set (ULift.up g')
  return action

/-- Creates a logic for a given constructor. This logic is combined with other
    method and constructor logics to create the complete resource logic for an
    object. -/
def Constructor.logic {lab : Label} {constrId : lab.ConstructorId}
  (constr : Class.Constructor constrId)
  (args : Class.Logic.Args lab)
  : Bool :=
    if args.isConsumed then
      match SomeType.cast args.data.memberArgs with
      | some argsData =>
        let newObj := constr.created argsData
        Class.Member.Logic.checkResourceData [newObj.toSomeObject] args.consumed
          && Class.Member.Logic.checkResourceData [newObj.toSomeObject] args.created
          && constr.invariant argsData
      | none =>
        false
    else
      -- TODO: not general enough, fine for the counter
      true

def Constructor.action {lab : Label} {constrId : lab.ConstructorId}
  (constr : Class.Constructor constrId) (key : Anoma.NullifierKey) (args : constrId.Args.type)
  : Rand Anoma.Action :=
    -- TODO: set nonce properly
    let newObj : Object lab := constr.created args
    let consumable : ConsumableObject lab :=
       { object := {newObj with nullifierKeyCommitment := Anoma.NullifierKeyCommitment.universal}
         ephemeral := true
         key := Anoma.NullifierKey.universal }
    let consumed : ConsumedObject lab := { consumable with can_nullify := Anoma.nullifyUniversal consumable.resource consumable.key rfl rfl }
    let createdResource : Anoma.Resource := newObj.toSomeObject.toResource (ephemeral := false) (nonce := consumed.can_nullify.nullifier.toNonce)
    let created : List CreatedObject :=
       [{ object := newObj
          resource := createdResource
          commitment := createdResource.commitment }]
    Action.create lab constrId args consumed created

/-- Creates an Anoma Transaction for a given object construtor. -/
def Constructor.transaction {lab : Label} {constrId : lab.ConstructorId}
  (constr : Class.Constructor constrId) (key : Anoma.NullifierKey) (args : constrId.Args.type)
  : Rand Anoma.Transaction := do
    let action ← constr.action key args
    pure <|
      { actions := [action],
        -- TODO: automatically generate deltaProof that verifies that the transaction is balanced
        deltaProof := "" }

/-- Creates a logic for a given method. This logic is combined with other method
    and constructor logics to create the complete resource logic for an object. -/
def Method.logic {lab : Label} {methodId : lab.MethodId}
  (method : Class.Method methodId)
  (args : Class.Logic.Args lab)
  : Bool :=
    if args.isConsumed then
      match SomeType.cast args.data.memberArgs with
      | some argsData =>
        let mselfObj : Option (Object lab) := Object.fromResource args.self
        match mselfObj with
          | none => false
          | some selfObj =>
            method.invariant selfObj argsData
            && Class.Member.Logic.checkResourceData [selfObj.toSomeObject] args.consumed
            && let createdObjects := method.created selfObj argsData
               Class.Member.Logic.checkResourceData createdObjects args.created
      | none =>
        false
    else
      -- TODO: may need to do something more here in general, fine for the counter
      true

def Method.action {lab : Label} (methodId : lab.MethodId) (method : Class.Method methodId) (self : Object lab) (key : Anoma.NullifierKey) (args : methodId.Args.type) : Option Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let consumable : ConsumableObject lab :=
      { key
        object := self
        ephemeral := false }
  match consumable.consume with
  | none => none
  | some consumed =>
    let createObject (o : SomeObject) : CreatedObject :=
      let res : Anoma.Resource := o.toResource (ephemeral := false) (nonce := Anoma.computeCreatedNonce key)
      { object := o.object
        resource := res
        commitment := res.commitment }
    let created : List CreatedObject :=
        List.map createObject (method.created self args)
    Action.create lab methodId args consumed created

/-- Creates an Anoma Transaction for a given object method. -/
def Method.transaction {lab : Label} (methodId : lab.MethodId) (method : Class.Method methodId) (self : Object lab) (key : Anoma.NullifierKey) (args : methodId.Args.type) : Option Anoma.Transaction := do
  let action ← method.action methodId self key args
  pure { actions := [action],
         -- TODO: set deltaProof properly
         deltaProof := "" }

/-- Creates a logic for a given destructor. This logic is combined with other
    member logics to create the complete resource logic for an object. -/
def Destructor.logic {lab : Label} {destructorId : lab.DestructorId}
  (destructor : Class.Destructor destructorId)
  (args : Class.Logic.Args lab)
  : Bool :=
    if args.isConsumed then
      match SomeType.cast args.data.memberArgs with
      | some argsData =>
        let mselfObj : Option (Object lab) := Object.fromResource args.self
        match mselfObj with
          | none => false
          | some selfObj =>
            Class.Member.Logic.checkResourceData [selfObj.toSomeObject] args.consumed
              && destructor.invariant selfObj argsData
      | none =>
        false
    else args.self.ephemeral

def Destructor.action {label : Label} (destructorId : label.DestructorId) (_destructor : Class.Destructor destructorId) (self : Object label) (key : Anoma.NullifierKey) (args : destructorId.Args.type) : Option Anoma.Action :=
  let consumable : ConsumableObject label :=
       { key
         object := self
         ephemeral := false }
  match consumable.consume with
  | none => none
  | some consumed =>
    let createdObject : CreatedObject :=
      let ephResource := { consumed.resource with ephemeral := true }
      { object := self
        resource := ephResource
        commitment := ephResource.commitment }
    Action.create label destructorId args consumed [createdObject]

/-- Creates an Anoma Transaction for a given object destructor. -/
def Destructor.transaction {lab : Label} (destructorId : lab.DestructorId) (destructor : Class.Destructor destructorId) (self : Object lab) (key : Anoma.NullifierKey) (args : destructorId.Args.type) : Option Anoma.Transaction := do
  let action ← destructor.action destructorId self key args
  pure { actions := [action],
         -- TODO: set deltaProof properly
         deltaProof := "" }

/-- Creates a member logic for a given intent. This logic is checked when an
  object is consumed to create the intent. Note that the intent member logic
  (defined here) is distinct from the intent logic defined in
  `AVM/Intent/Translation.lean`. The intent member logic is associated with
  a resource consumed by the intent and it checks that the right intent is
  created. The intent logic is checked on consumption of the intent resource
  and it checks that the the intent's condition is satified. -/
def Intent.logic {lab : Label} (intent : Intent) (args : Class.Logic.Args lab) : Bool :=
  if args.isConsumed then
    -- Check that exactly one resource is created that corresponds to the intent
    match Class.Member.Logic.filterOutDummy args.created with
    | [intentRes] => BoolCheck.run do
      let labelData ← BoolCheck.some <| Intent.LabelData.fromResource intentRes
      BoolCheck.ret <|
        -- NOTE: We should also check that the intent logic hashes of
        -- `intentRes` and `intent` match.
        labelData.label === intent.label
        && intentRes.quantity == 1
        && intentRes.ephemeral
        && Member.Logic.checkResourceData labelData.data.provided args.consumed
    | _ =>
      false
  else
    true

private def logic' {lab : Label} (cls : Class lab) (args : Class.Logic.Args lab) : Bool :=
  -- Check if the logic is consumed. We should not rely on app data (args.data)
  -- to detect the consumed case, because then someone could simply turn
  -- off the checks by providing malicious app data
  if args.isConsumed then
    -- Check:
    -- 1. member logic corresponding to the memberId in AppData
    -- 2. class invariant for the object being consumed
    BoolCheck.run do
      let selfObj : Object lab ← BoolCheck.some (Object.fromResource args.self)
      BoolCheck.ret <|
        checkMemberLogic args.data.memberId
        && cls.invariant selfObj args
  else
    true
  where
    checkMemberLogic (memberId : Label.MemberId lab) : Bool :=
      match memberId with
      | .constructorId c =>
        Class.Constructor.logic (cls.constructors c) args
      | .methodId m =>
        Class.Method.logic (cls.methods m) args
      | .destructorId m =>
        Class.Destructor.logic (cls.destructors m) args
      | .intentId i =>
        Class.Intent.logic (cls.intents i) args
      | .falseLogicId =>
        false

def logic {lab : Label} (cls : Class lab) (args : Anoma.Logic.Args SomeAppData) : Bool :=
  match tryCast args.data.appData with
  | none => false
  | some appData =>
    logic' cls { args with data := appData }
