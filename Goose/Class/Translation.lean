
import Utils
import Anoma
import Goose.Class
import Goose.Class.Member
import Goose.Class.Member.Logic

namespace Goose

/-- Helper function to create an Action. -/
def Action.create {sig : Signature} {Args : Type} [rawArgs : Anoma.Raw Args] (args : Args)
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
def Class.Constructor.logic (sig : Signature) (constr : Class.Constructor sig) (args : Anoma.Logic.Args (constr.AppData sig.pub)) : Bool :=
  let argsData : constr.Args := args.data.args
  let newObj := constr.created argsData
  if args.isConsumed then
    Class.Member.Logic.checkResourceData [newObj] args.consumed
      && Class.Member.Logic.checkResourceData [newObj] args.created
      && constr.extraLogic argsData
  else
    True

def Class.Constructor.action (sig : Signature) (constr : Class.Constructor sig) (args : constr.Args) : Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let newObj : Object sig := constr.created args
  let ephRes : Anoma.Resource := Object.toResource (ephemeral := true) newObj
  let newRes : Anoma.Resource := Object.toResource (ephemeral := false) newObj
  Action.create
    (rawArgs := constr.rawArgs)
    args
    (consumedLogics := [constr.logic])
    (createdLogics := [trueLogic])
    (consumedObjects := [newObj])
    (createdObjects := [newObj])
    (consumedResources := [ephRes])
    (createdResources := [newRes])

/-- Creates an Anoma Transaction for a given object construtor. -/
def Class.Constructor.transaction (sig : Signature) (constr : Class.Constructor sig) (args : constr.Args) (currentRoot : Anoma.CommitmentRoot) : Anoma.Transaction :=
  let action := constr.action sig args
  { roots := [currentRoot],
    actions := [action],
    -- TODO: set deltaProof properly
    deltaProof := "" }

/-- Creates a logic for a given method. This logic is combined with other method
    and constructor logics to create the complete resource logic for an object. -/
def Class.Method.logic (sig : Signature) (method : Class.Method sig) (args : Anoma.Logic.Args method.AppData) : Bool :=
  let publicFields : Public.PublicFields sig.pub := args.data.publicFields
  let argsData : method.Args := args.data.args
  -- let selfObj := @Object.fromResource _ args.data.rawPublicFields publicFields args.self
  let mselfObj : Option (Object sig) := Object.fromResource publicFields args.self
  match mselfObj with
    | none => False
    | (some selfObj) =>

    let createdObjects := method.created selfObj argsData
    if args.isConsumed then
      Class.Member.Logic.checkResourceData [selfObj] args.consumed
        && Class.Member.Logic.checkResourceData createdObjects args.created
        && method.extraLogic selfObj argsData
    else
      True

def Class.Method.action (sig : Signature) (method : Class.Method sig) (self : Object sig) (args : method.Args) : Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let consumedObjects := [self]
  let consumedResources := List.map Object.toResource consumedObjects
  let createdObjects := method.created self args
  let createdResources := List.map Object.toResource createdObjects
  Action.create
    (rawArgs := method.rawArgs)
    args
    (consumedLogics := [method.logic])
    (createdLogics := [trueLogic])
    consumedObjects
    createdObjects
    consumedResources
    createdResources

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
