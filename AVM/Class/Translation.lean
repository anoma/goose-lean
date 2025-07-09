
import Prelude
import Anoma
import AVM.Class
import AVM.Class.Member
import AVM.Class.Member.Logic

namespace AVM.Class

private structure CreatedObject where
  {label : Label}
  object : Object label
  resource : Anoma.Resource
  commitment : Anoma.Commitment

private structure ConsumedObject (lab : Label) where
  object : Object lab
  resource : Anoma.Resource
  nullifier : Anoma.Nullifier

/-- Helper function to create an Action. -/
private def Action.create (lab : Label) (memberId : Label.MemberId lab) (args : memberId.Args.type)
  (consumed : ConsumedObject lab)
  (created : List CreatedObject) -- no appdata/logic
  : Anoma.Action :=
  let appData : Std.HashMap Anoma.Tag Class.SomeAppData :=
    Std.HashMap.emptyWithCapacity
    |>.insertMany [mkTagDataPairConsumed consumed]
    |>.insertMany (List.map mkTagDataPairCreated created)
  { Data := ⟨Class.SomeAppData⟩,
    consumed := [(Anoma.RootedNullifiableResource.Transparent.fromResource ∘ ConsumedObject.resource) consumed],
    created := List.map CreatedObject.resource created,
    appData }
  where
    mkTagDataPairConsumed (i : ConsumedObject lab)
     : Anoma.Tag × Class.SomeAppData :=
      (Anoma.Tag.Consumed i.nullifier,
        { appData := {
            memberId,
            memberArgs := args,
            publicFields := i.object.publicFields
        }})

    mkTagDataPairCreated (i : CreatedObject)
     : Anoma.Tag × Class.SomeAppData :=
      (Anoma.Tag.Created i.commitment,
        {label := i.label,
         appData := {
          memberId := Label.MemberId.falseLogicId,
          memberArgs := UUnit.unit,
          publicFields := i.object.publicFields
        }})

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
  (constr : Class.Constructor constrId) (args : constrId.Args.type)
  : Anoma.Action :=
    -- TODO: set nonce properly
    let newObj : Object lab := constr.created args
    let ephRes : Anoma.Resource := {SomeObject.toResource (ephemeral := true) newObj.toSomeObject with nullifierKeyCommitment := Anoma.NullifierKeyCommitment.universal}
    let rootedEph : Anoma.RootedNullifiableResource :=
           { key := Anoma.NullifierKey.universal
             resource := ephRes
             root := Anoma.CommitmentRoot.todo }
    let ⟨null, _⟩ := Anoma.nullifyUniversal rootedEph rfl rfl
    let newRes : Anoma.Resource := SomeObject.toResource (ephemeral := false) newObj.toSomeObject
    let consumed : ConsumedObject lab := { object := newObj
                                           nullifier := null
                                           resource := ephRes }
    let created : List CreatedObject :=
       [{ object := newObj
          resource := newRes
          commitment := newRes.commitment }]
    Action.create lab constrId args consumed created

/-- Creates an Anoma Transaction for a given object construtor. -/
def Constructor.transaction {lab : Label} {constrId : lab.ConstructorId}
  (constr : Class.Constructor constrId) (args : constrId.Args.type) (currentRoot : Anoma.CommitmentRoot)
  : Anoma.Transaction :=
    let action := constr.action args
    { roots := [currentRoot],
      actions := [action],
      -- TODO: automatically generate deltaProof that verifies that the transaction is balanced
      deltaProof := "" }

/-- Creates a logic for a given method. This logic is combined with other method
    and constructor logics to create the complete resource logic for an object. -/
def Method.logic {lab : Label} {methodId : lab.MethodId}
  (method : Class.Method methodId)
  (publicFields : lab.PublicFields.type)
  (args : Class.Logic.Args lab)
  : Bool :=
    if args.isConsumed then
      match SomeType.cast args.data.memberArgs with
      | some argsData =>
        let mselfObj : Option (Object lab) := Object.fromResource publicFields args.self
        match mselfObj with
          | none => false
          | (some selfObj) =>
            let createdObjects := method.created selfObj argsData
            Class.Member.Logic.checkResourceData [selfObj.toSomeObject] args.consumed
              && Class.Member.Logic.checkResourceData createdObjects args.created
              && method.invariant selfObj argsData
      | none =>
        false
    else
      -- TODO: may need to do something more here in general, fine for the counter
      true

def Method.action {lab : Label} (methodId : lab.MethodId) (method : Class.Method methodId) (self : Object lab) (key : Option Anoma.NullifierKey) (args : methodId.Args.type) : Option Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let resource := self.toSomeObject.toResource
  let nullRes : Anoma.RootedNullifiableResource := {
    key := key.getD Anoma.NullifierKey.universal
    resource
    root := Anoma.CommitmentRoot.todo
   }
  match Anoma.nullify nullRes with
  | none => none
  | (some nullifier) =>
    let consumed : ConsumedObject lab :=
      { object := self
        nullifier
        resource := self.toSomeObject.toResource }
    let createObject (o : SomeObject) : CreatedObject  :=
      let res := o.toResource
      { object := o.object
        resource := res
        commitment := res.commitment }
    let created : List CreatedObject :=
        List.map createObject (method.created self args)
    Action.create lab methodId args consumed created

/-- Creates an Anoma Transaction for a given object method. -/
def Method.transaction {lab : Label} (methodId : lab.MethodId) (method : Class.Method methodId) (self : Object lab) (key : Option Anoma.NullifierKey) (args : methodId.Args.type) (currentRoot : Anoma.CommitmentRoot) : Option Anoma.Transaction := do
  let action ← method.action methodId self key args
  pure { roots := [currentRoot],
         actions := [action],
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
    match args.created with
    | [intentRes] => BoolCheck.run do
      let data ← BoolCheck.some <| Intent.ResourceData.fromResource intentRes
      BoolCheck.ret <|
        -- NOTE: We should also check that the intent logic hashes of
        -- `intentRes` and `intent` match.
        intentRes.label === intent.label
        && intentRes.quantity == 1
        && intentRes.ephemeral
        && Member.Logic.checkResourceData data.provided args.consumed
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
      let selfObj : Object lab ← BoolCheck.some (Object.fromResource args.data.publicFields args.self)
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
        Class.Method.logic (cls.methods m) args.data.publicFields args
      | .intentId i =>
        Class.Intent.logic (cls.intents i) args
      | .falseLogicId =>
        false

def logic {lab : Label} (cls : Class lab) (args : Anoma.Logic.Args SomeAppData) : Bool :=
  match tryCast args.data.appData with
  | none => false
  | some appData =>
    logic' cls { args with data := appData }
