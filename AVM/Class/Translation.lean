
import Prelude
import Anoma
import AVM.Class
import AVM.Class.Member
import AVM.Class.Member.Logic

namespace AVM.Class

private structure CreatedObject : Type (u + 2) where
  {lab : Label}
  object : Object lab
  resource : Anoma.Resource.{u}

private structure ConsumedObject (sig : Label) : Type (u + 2) where
  object : Object sig
  resource : Anoma.Resource.{u}

/-- Helper function to create an Action. -/
private def Action.create {lab : Label} (memberId : MemberId lab) (args : memberId.Args)
  (consumed : ConsumedObject lab)
  (created : List CreatedObject) -- no appdata/logic
  : Anoma.Action :=
  -- appData for each resource consists of:
  -- 1. action logic (indicator)
  -- 2. the public data of the object
  -- 3. the action (method/constructor) arguments
  let appData : Std.HashMap Anoma.Tag Class.SomeAppData :=
    Std.HashMap.emptyWithCapacity
    |>.insertMany [mkTagDataPairConsumed consumed]
    |>.insertMany (List.map mkTagDataPair created)
  { Data := Class.SomeAppData,
    consumed := [(Anoma.RootedNullifiableResource.Transparent.fromResource ∘ ConsumedObject.resource) consumed],
    created := List.map CreatedObject.resource created,
    appData }
  where
    mkTagDataPairConsumed (i : ConsumedObject lab)
     : Anoma.Tag × Class.SomeAppData :=
      (Anoma.Tag.fromResource (isConsumed := True) i.resource,
        { appData :=
         { publicFields := i.object.publicFields
           memberSomeAppData := some {
            memberId
            appData := {args}}}})

    mkTagDataPair (i : CreatedObject)
     : Anoma.Tag × Class.SomeAppData :=
      (Anoma.Tag.fromResource (isConsumed := False) i.resource,
        {lab := i.lab,
         appData := {publicFields := i.object.publicFields
                     memberSomeAppData := none}})

/-- Creates a logic for a given constructor. This logic is combined with other
    method and constructor logics to create the complete resource logic for an
    object. -/
def Constructor.logic {lab : Label} {constrId : lab.ConstructorId}
  (constr : Class.Constructor constrId)
  (args : Anoma.Logic.Args constrId.Args)
  : Bool :=
    let argsData : constrId.Args := args.data
    let newObj := constr.created argsData
    if args.isConsumed then
      Class.Member.Logic.checkResourceData [newObj.toSomeObject] args.consumed
        && Class.Member.Logic.checkResourceData [newObj.toSomeObject] args.created
        && constr.extraLogic argsData
    else
      -- TODO: not general enough, fine for the counter
      True

def Constructor.action {lab : Label} {constrId : lab.ConstructorId}
  (constr : Class.Constructor constrId) (args : constrId.Args)
  : Anoma.Action :=
    -- TODO: set nonce and nullifierKeyCommitment properly
    let newObj : Object lab := constr.created args
    let ephRes : Anoma.Resource := SomeObject.toResource (ephemeral := true) newObj.toSomeObject
    let newRes : Anoma.Resource := SomeObject.toResource (ephemeral := false) newObj.toSomeObject
    let consumed : ConsumedObject lab := { object := newObj
                                           resource := ephRes }
    let created : List CreatedObject :=
       [{
          object := newObj
          resource := newRes }]
    @Action.create lab constrId args consumed created

/-- Creates an Anoma Transaction for a given object construtor. -/
def Constructor.transaction {lab : Label} {constrId : lab.ConstructorId}
  (constr : Class.Constructor constrId) (args : constrId.Args) (currentRoot : Anoma.CommitmentRoot)
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
  (publicFields : lab.pub.PublicFields)
  (args : Anoma.Logic.Args (Class.Method.AppData methodId))
  : Bool :=
    let argsData : methodId.Args := args.data.args
    let mselfObj : Option (Object lab) := Object.fromResource publicFields args.self
    match mselfObj with
      | none => False
      | (some selfObj) =>
        let createdObjects := method.created selfObj argsData
        if args.isConsumed then
          Class.Member.Logic.checkResourceData [selfObj.toSomeObject] args.consumed
            && Class.Member.Logic.checkResourceData createdObjects args.created
            && method.extraLogic selfObj argsData
        else
          -- NOTE thise branch is never hit because we don't add AppData for created resources
          -- TODO: may need to do something more here in general, fine for the counter
          True

def Method.action {lab : Label} (methodId : lab.MethodId) (method : Class.Method methodId) (self : Object lab) (args : methodId.Args) : Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let consumed : ConsumedObject lab :=
       { object := self
         resource := self.toSomeObject.toResource }
  let createObject (o : SomeObject) : CreatedObject  :=
       { object := o.object
         resource := o.toResource }
  let created : List CreatedObject :=
       List.map createObject (method.created self args)
  Action.create (MemberId.methodId methodId) args consumed created

/-- Creates an Anoma Transaction for a given object method. -/
def Method.transaction (lab : Label) (methodId : lab.MethodId) (method : Class.Method methodId) (self : Object lab) (args : methodId.Args) (currentRoot : Anoma.CommitmentRoot) : Anoma.Transaction :=
  let action := method.action methodId self args
  { roots := [currentRoot],
    actions := [action],
    -- TODO: set deltaProof properly
    deltaProof := "" }

-- TODO make it prettier by avoiding nested matches
def logic (lab : Label) (cls : Class lab)
  (args : Anoma.Logic.Args (Class.AppData lab))
  : Bool := BoolCheck.run do
    let mself : Object lab <- BoolCheck.some (Object.fromResource args.data.publicFields args.self)
    -- NOTE We have AppData iff the object is being consumed (as self)
    -- TODO: we should not rely on app data to detect the consumed case,
    -- because in this way someone can simply turn off the checks by
    -- providing malicious app data
    let someAppData : Member.SomeAppData lab <- BoolCheck.someOr args.data.memberSomeAppData True
    let memberId : MemberId lab := someAppData.memberId
    let memArgs : memberId.Args := someAppData.appData.args
    match x : memberId with
      | MemberId.constructorId c =>
        BoolCheck.guard (Class.Constructor.logic (cls.constructors c)
          -- TODO how to do this without tactics?
          {args with data := by {
              rw [x] at memArgs
              apply memArgs }})
      | MemberId.methodId m =>
        BoolCheck.guard (Class.Method.logic (cls.methods m)
          args.data.publicFields
          -- TODO how to do this without tactics?
          {args with data := by {
            constructor
            rw [<- x]
            apply memArgs }})
