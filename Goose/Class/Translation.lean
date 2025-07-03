
import Prelude
import Anoma
import Goose.Class
import Goose.Class.Member
import Goose.Class.Member.Logic

namespace Goose

structure CreatedObject : Type 1 where
  {sig : Signature}
  object : Object sig
  resource : Anoma.Resource

structure ConsumedObject (sig : Signature) : Type 1 where
  object : Object sig
  resource : Anoma.Resource

/-- Helper function to create an Action. -/
def Action.create {sig : Signature} (memberId : MemberId sig) (args : memberId.Args)
  (consumed : ConsumedObject sig)
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
    mkTagDataPairConsumed (i : ConsumedObject sig)
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
        {sig := i.sig,
         appData := {publicFields := i.object.publicFields
                     memberSomeAppData := none}})

/-- Creates a logic for a given constructor. This logic is combined with other
    method and constructor logics to create the complete resource logic for an
    object. -/
def Class.Constructor.logic {sig : Signature} {constrId : sig.ConstructorId}
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

def Class.Constructor.action {sig : Signature} {constrId : sig.ConstructorId}
  (constr : Class.Constructor constrId) (args : constrId.Args)
  : Anoma.Action :=
    -- TODO: set nonce and nullifierKeyCommitment properly
    let newObj : Object sig := constr.created args
    let ephRes : Anoma.Resource := SomeObject.toResource (ephemeral := true) newObj.toSomeObject
    let newRes : Anoma.Resource := SomeObject.toResource (ephemeral := false) newObj.toSomeObject
    let consumed : ConsumedObject sig := { object := newObj
                                           resource := ephRes }
    let created : List CreatedObject :=
       [{
          object := newObj
          resource := newRes }]
    @Action.create sig constrId args consumed created

/-- Creates an Anoma Transaction for a given object construtor. -/
def Class.Constructor.transaction {sig : Signature} {constrId : sig.ConstructorId}
  (constr : Class.Constructor constrId) (args : constrId.Args) (currentRoot : Anoma.CommitmentRoot)
  : Anoma.Transaction :=
    let action := constr.action args
    { roots := [currentRoot],
      actions := [action],
      -- TODO: automatically generate deltaProof that verifies that the transaction is balanced
      deltaProof := "" }

/-- Creates a logic for a given method. This logic is combined with other method
    and constructor logics to create the complete resource logic for an object. -/
def Class.Method.logic {sig : Signature} {methodId : sig.MethodId}
  (method : Class.Method methodId)
  (publicFields : sig.pub.PublicFields)
  (args : Anoma.Logic.Args (Class.Method.AppData methodId))
  : Bool :=
    let argsData : methodId.Args := args.data.args
    let mselfObj : Option (Object sig) := Object.fromResource publicFields args.self
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

def Class.Method.action {sig : Signature} (methodId : sig.MethodId) (method : Class.Method methodId) (self : Object sig) (args : methodId.Args) : Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let consumed : ConsumedObject sig :=
       { object := self
         resource := self.toSomeObject.toResource }
  let createObject (o : SomeObject) : CreatedObject  :=
       { object := o.object
         resource := o.toResource }
  let created : List CreatedObject :=
       List.map createObject (method.created self args)
  Action.create (MemberId.methodId methodId) args consumed created

/-- Creates an Anoma Transaction for a given object method. -/
def Class.Method.transaction (sig : Signature) (methodId : sig.MethodId) (method : Class.Method methodId) (self : Object sig) (args : methodId.Args) (currentRoot : Anoma.CommitmentRoot) : Anoma.Transaction :=
  let action := method.action methodId self args
  { roots := [currentRoot],
    actions := [action],
    -- TODO: set deltaProof properly
    deltaProof := "" }

-- TODO make it prettier by avoiding nested matches
def Class.logic (sig : Signature) (cls : Class sig)
  (args : Anoma.Logic.Args (Class.AppData sig))
  : Bool :=
    let mself : Option (Object sig) := Object.fromResource args.data.publicFields args.self
    match mself with
      | none => False
      | (some self) =>
        let msomeAppData : Option (Member.SomeAppData sig) := args.data.memberSomeAppData
        match msomeAppData with
          | none => True
          -- NOTE this is 'some' iff the object is being consumed (as self)
          | (some someAppData) =>
            let memberId : MemberId sig := someAppData.memberId
            let memArgs : memberId.Args := someAppData.appData.args
            match x : memberId with
              | MemberId.constructorId c =>
                Class.Constructor.logic (cls.constructors c)
                  -- TODO how to do this without tactics?
                  {args with data := by {
                      rw [x] at memArgs
                      apply memArgs }}

              | MemberId.methodId m =>
                Class.Method.logic (cls.methods m)
                  args.data.publicFields
                  -- TODO how to do this without tactics?
                  {args with data := by {
                    constructor
                    rw [<- x]
                    apply memArgs }}

end Goose
