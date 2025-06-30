
import Prelude
import Anoma
import Goose.Class
import Goose.Class.Member
import Goose.Class.Member.Logic

namespace Goose

structure ActionItem (c : ConsumedCreated) (Args : Type) : Type 1 where
  {sig : Signature}
  logic : Class.Member.Logic sig.pub Args
  object : Object sig
  resource : Anoma.Resource

/-- Helper function to create an Action. -/
def Action.create {Args : Type} [rawArgs : Anoma.Raw Args] (args : Args)
  (consumed : List (ActionItem Consumed Args))
  (created : List (ActionItem Created Args))
  : Anoma.Action :=
  -- appData for each resource consists of:
  -- 1. action logic (indicator)
  -- 2. the public data of the object
  -- 3. the action (method/constructor) arguments
  let appData : Std.HashMap Anoma.Tag Class.SomeAppData :=
    Std.HashMap.emptyWithCapacity
    |>.insertMany (List.map mkTagDataPair consumed)
    |>.insertMany (List.map mkTagDataPair created)
  { Data := Class.SomeAppData,
    consumed := List.map (Anoma.RootedNullifiableResource.Transparent.fromResource ∘ ActionItem.resource) consumed,
    created := List.map ActionItem.resource created,
    appData }
  where
    mkTagDataPair {c : ConsumedCreated} (i : ActionItem c Args)
     : Anoma.Tag × Class.SomeAppData :=
      (Anoma.Tag.fromResource (c.isConsumed ) i.resource,
        { appData :=
         { Args := Args,
           memberAppData := Class.Member.appData i.sig i.object args,
           memberLogic := i.logic }})

def Action.create.old {sig : Signature} {Args : Type} [rawArgs : Anoma.Raw Args] (args : Args)
  (consumedLogics createdLogics : List (Class.Member.Logic sig.pub Args))
  (consumedObjects createdObjects : List (Object sig))
  (consumedResources createdResources : List Anoma.Resource)
  : Anoma.Action :=
  -- appData for each resource consists of:
  -- 1. action logic (indicator)
  -- 2. the public data of the object
  -- 3. the action (method/constructor) arguments
  let appData : Std.HashMap Anoma.Tag (Class.AppData sig.pub) :=
    Std.HashMap.emptyWithCapacity
    |>.insertMany (List.zipWith3Exact (mkTagDataPair (isConsumed := true)) consumedLogics consumedObjects consumedResources)
    |>.insertMany (List.zipWith3Exact (mkTagDataPair (isConsumed := false)) createdLogics createdObjects createdResources)
  { Data := Class.AppData sig.pub,
    consumed := List.map Anoma.RootedNullifiableResource.Transparent.fromResource consumedResources,
    created := createdResources,
    appData }
  where
    mkTagDataPair (isConsumed : Bool) (memberLogic : Class.Member.Logic sig.pub Args) (obj : Object sig) (res : Anoma.Resource)
     : Anoma.Tag × Class.AppData sig.pub :=
      (Anoma.Tag.fromResource isConsumed res,
        { Args := Args,
          memberAppData := Class.Member.appData sig obj args,
          memberLogic
        })

/-- Creates a logic for a given constructor. This logic is combined with other
    method and constructor logics to create the complete resource logic for an
    object. -/
def Class.Constructor.logic (sig : Signature) (constr : Class.Constructor sig) (args : Anoma.Logic.Args constr.AppData) : Bool :=
  let argsData : constr.Args := args.data.args
  let newObj := constr.created argsData
  if args.isConsumed then
    Class.Member.Logic.checkResourceData [newObj.toSomeObject] args.consumed
      && Class.Member.Logic.checkResourceData [newObj.toSomeObject] args.created
      && constr.extraLogic argsData
  else
    True

def Class.Constructor.action (sig : Signature) (constr : Class.Constructor sig) (args : constr.Args) : Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let newObj : Object sig := constr.created args
  let ephRes : Anoma.Resource := SomeObject.toResource (ephemeral := true) newObj.toSomeObject
  let newRes : Anoma.Resource := SomeObject.toResource (ephemeral := false) newObj.toSomeObject
  let consumed : List (ActionItem Consumed constr.Args) :=
     [{ logic := constr.logic
        object := newObj
        resource := ephRes }]
  let created : List (ActionItem Created constr.Args) :=
     [{ logic := trueLogic
        object := newObj
        resource := newRes }]
  Action.create (rawArgs := constr.rawArgs) args consumed created

/-- Creates an Anoma Transaction for a given object construtor. -/
def Class.Constructor.transaction (sig : Signature) (constr : Class.Constructor sig) (args : constr.Args) (currentRoot : Anoma.CommitmentRoot) : Anoma.Transaction :=
  let action := constr.action sig args
  { roots := [currentRoot],
    actions := [action],
    -- TODO: automatically generate deltaProof that verifies that the transaction is balanced
    deltaProof := "" }

/-- Creates a logic for a given method. This logic is combined with other method
    and constructor logics to create the complete resource logic for an object. -/
def Class.Method.logic (sig : Signature) (method : Class.Method sig) (args : Anoma.Logic.Args method.AppData) : Bool :=
  let publicFields : sig.pub.PublicFields := args.data.publicFields
  let argsData : method.Args := args.data.args
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
        -- TODO: may need to do something more here in general, fine for the counter
        True

def Class.Method.action (sig : Signature) (method : Class.Method sig) (self : Object sig) (args : method.Args) : Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let consumed : List (ActionItem Consumed method.Args) :=
       [{ logic := method.logic
          object := self
          resource := self.toSomeObject.toResource }]
  let createdItem (o : SomeObject) : ActionItem Created method.Args :=
       { logic := trueLogic
         object := o.object
         resource := o.toResource }
  let created : List (ActionItem Created method.Args) :=
       List.map createdItem (method.created self args)
  Action.create (rawArgs := method.rawArgs) args consumed created

/-- Creates an Anoma Transaction for a given object method. -/
def Class.Method.transaction (sig : Signature) (method : Class.Method sig) (self : Object sig) (args : method.Args) (currentRoot : Anoma.CommitmentRoot) : Anoma.Transaction :=
  let action := method.action sig self args
  { roots := [currentRoot],
    actions := [action],
    -- TODO: set deltaProof properly
    deltaProof := "" }

def Class.logic (sig : Signature) (cls : Class sig) (args : Anoma.Logic.Args (Class.AppData sig.pub)) : Bool :=
  let mselfObj : Option (Object sig) := @Object.fromResource sig args.data.memberAppData.publicFields args.self
  match mselfObj with
    | none => False
    | (some selfObj) =>
      let memberLogicArgs := { args with data := args.data.memberAppData }
      let extraLogicArgs := { args with data := { args.data.memberAppData with args := () } }
      -- In a real implementation, there is a fixed finite number of action logics
      -- (constructor and method logics). The action logics are identified by enum
      -- values and we make a big case switch here instead of the first conjunct to
      -- choose an appropriate action logic. In Lean, it is clearer and more
      -- convenient to store the action logic function directly in appData, instead
      -- of storing its identifying enum value.
      args.data.memberLogic memberLogicArgs
        && cls.extraLogic selfObj extraLogicArgs

end Goose
