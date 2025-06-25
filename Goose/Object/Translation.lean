
import Goose.Object
import Goose.Class
import Goose.Logic
import Anoma

namespace Goose

def Object.toResource (obj : Object) (ephemeral := false) (nonce := 0) (nullifierKeyCommitment := "") : Anoma.Resource :=
  { Val := obj.PrivateData,
    rawVal := obj.rawPrivateData,
    label := obj.classLabel,
    quantity := obj.quantity,
    value := obj.privateData,
    ephemeral := ephemeral,
    nonce,
    nullifierKeyCommitment }

def Object.fromResource {Data} [Anoma.Raw Data] (publicData : Data) (res : Anoma.Resource) : Object :=
  { PrivateData := res.Val,
    PublicData := Data,
    rawPrivateData := res.rawVal,
    quantity := res.quantity,
    privateData := res.value,
    publicData := publicData,
    classLabel := res.label }

def Object.appData {Args} (self : Object) (args : Args) : Object.AppData Args :=
  { PublicData := self.PublicData,
    rawPublicData := self.rawPublicData,
    publicData := self.publicData,
    args }

/-- Checks that the number of objects and resources match, and that the
      resources' private data and labels match the objects' private data and
      labels. This check is used in the constructor and method logics. -/
def Logic.checkResourceData (objects : List Object) (resources : List Anoma.Resource) : Bool :=
  objects.length == resources.length
    && List.and (List.zipWith resourceDataEq objects resources)
  where
    resourceDataEq (obj : Object) (res : Anoma.Resource) : Bool :=
      @Anoma.rawEq _ _ res.rawVal obj.rawPrivateData res.value obj.privateData
        && res.label == obj.classLabel

/-- Helper function to create an Action. -/
def Action.create {Args} [Anoma.Raw Args] (args : Args)
  (consumedActionLogics createdActionLogics : List (Action.Logic Args))
  (consumedObjects createdObjects : List Object)
  (consumedResources createdResources : List Anoma.Resource) : Anoma.Action :=
  -- appData for each resource consists of:
  -- 1. action logic (indicator)
  -- 2. the public data of the object
  -- 3. the action (method/constructor) arguments
  let appData : Std.HashMap Anoma.Tag Class.AppData :=
    Std.HashMap.emptyWithCapacity
    |>.insertMany (List.zipWith (Function.uncurry (mkTagDataPair (isConsumed := true))) (List.zip consumedActionLogics consumedObjects) consumedResources)
    |>.insertMany (List.zipWith (Function.uncurry (mkTagDataPair (isConsumed := false))) (List.zip createdActionLogics createdObjects) createdResources)
  { Data := Class.AppData,
    consumed := List.map Anoma.RootedNullifiableResource.Transparent.fromResource consumedResources,
    created := createdResources,
    appData }
  where
    mkTagDataPair (isConsumed : Bool) (actionLogic : Action.Logic Args) (obj : Object) (res : Anoma.Resource) : Anoma.Tag × Class.AppData :=
      (Anoma.Tag.fromResource isConsumed res,
        { Args := Args,
          objectAppData := obj.appData args,
          actionLogic
        })

/-- Creates a logic for a given constructor. This logic is combined with other
      method and constructor logics to create the complete resource logic for an
      object. See `Goose.Class` and `Goose.Class.Translation`. -/
def Object.Constructor.logic (constr : Object.Constructor) (args : Anoma.Logic.Args constr.AppData) : Bool :=
  let argsData : constr.Args := args.data.args
  let newObj := constr.created argsData
  if args.isConsumed then
    Logic.checkResourceData [newObj] args.consumed
      && Logic.checkResourceData [newObj] args.created
      && constr.extraLogic argsData
  else
    True

def Object.Constructor.action (constr : Object.Constructor) (args : constr.Args) : Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let newObj : Object := constr.created args
  let ephRes : Anoma.Resource := Object.toResource (ephemeral := true) newObj
  let newRes : Anoma.Resource := Object.toResource (ephemeral := false) newObj
  @Action.create _ constr.rawArgs args [constr.logic] [trueLogic] [newObj] [newObj] [ephRes] [newRes]

/-- Creates an Anoma Transaction for a given object construtor. -/
def Object.Constructor.transaction (constr : Object.Constructor) (args : constr.Args) (currentRoot : Anoma.CommitmentRoot) : Anoma.Transaction :=
  let action := constr.action args
  { roots := [currentRoot],
    actions := [action],
    -- TODO: set deltaProof properly
    deltaProof := "" }

/-- Creates a logic for a given method. This logic is combined with other method
    and constructor logics to create the complete resource logic for an object.
    See `Goose.Class` and `Goose.Class.Translation`. -/
def Object.Method.logic (method : Object.Method) (args : Anoma.Logic.Args method.AppData) : Bool :=
  let publicData : args.data.PublicData := args.data.publicData
  let argsData : method.Args := args.data.args
  let selfObj := @Object.fromResource _ args.data.rawPublicData publicData args.self
  let createdObjects := method.created selfObj argsData
  if args.isConsumed then
    Logic.checkResourceData [selfObj] args.consumed
      && Logic.checkResourceData createdObjects args.created
      && method.extraLogic selfObj argsData
  else
    True

def Object.Method.action (method : Object.Method) (self : Object) (args : method.Args) : Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let consumedObjects := [self]
  let consumedResources := List.map Object.toResource consumedObjects
  let createdObjects := method.created self args
  let createdResources := List.map Object.toResource createdObjects
  @Action.create _ method.rawArgs args
    [method.logic] [trueLogic]
    consumedObjects createdObjects
    consumedResources createdResources

/-- Creates an Anoma Transaction for a given object method. -/
def Object.Method.transaction (method : Object.Method) (self : Object) (args : method.Args) (currentRoot : Anoma.CommitmentRoot) : Anoma.Transaction :=
  let action := method.action self args
  { roots := [currentRoot],
    actions := [action],
    -- TODO: set deltaProof properly
    deltaProof := "" }

end Goose
