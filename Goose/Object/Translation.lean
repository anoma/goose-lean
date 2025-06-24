
import Goose.Object
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

def Logic.checkResourceData (objects : List Object) (resources : List Anoma.Resource) : Bool :=
  objects.length == resources.length
    && List.and (List.zipWith resourceDataEq objects resources)
  where
    resourceDataEq (obj : Object) (res : Anoma.Resource) : Bool :=
      @Anoma.rawEq _ _ res.rawVal obj.rawPrivateData res.value obj.privateData
        && res.label == obj.classLabel

def Action.create {Args} [Anoma.Raw Args] (args : Args)
  (consumedObjects createdObjects : List Object)
  (consumedResources createdResources : List Anoma.Resource) : Anoma.Action :=
  -- appData for each resource consists of:
  -- 1. the public data of the object
  -- 2. the method arguments
  let appData : Std.HashMap Anoma.Tag (Object.AppData Args) :=
    Std.HashMap.emptyWithCapacity
    |>.insertMany (List.zipWith (fun obj res => (Anoma.Tag.fromResource (isConsumed := true) res, obj.appData args)) consumedObjects consumedResources)
    |>.insertMany (List.zipWith (fun obj res => (Anoma.Tag.fromResource (isConsumed := false) res, obj.appData args)) createdObjects createdResources)
  { Data := (Object.AppData Args),
    consumed := List.map Anoma.RootedNullifiableResource.Transparent.fromResource consumedResources,
    created := createdResources,
    appData }

def Object.Constructor.logic (constr : Object.Constructor) (args : Anoma.Logic.Args constr.AppData) : Bool :=
  let argsData : constr.Args := args.data.args
  let newObj := constr.created argsData
  Logic.checkResourceData [newObj] args.consumed
    && Logic.checkResourceData [newObj] args.created
    && constr.extraLogic argsData

def Object.Constructor.action (constr : Object.Constructor) (args : constr.Args) : Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let newObj : Object := constr.created args
  let ephRes : Anoma.Resource := Object.toResource (ephemeral := true) newObj
  let newRes : Anoma.Resource := Object.toResource (ephemeral := false) newObj
  @Action.create _ constr.rawArgs args [newObj] [newObj] [ephRes] [newRes]

def Object.Constructor.transaction (constr : Object.Constructor) (args : constr.Args) (currentRoot : Anoma.CommitmentRoot) : Anoma.Transaction :=
  let action := constr.action args
  { roots := [currentRoot],
    actions := [action],
    -- TODO: set deltaProof properly
    deltaProof := "" }

def Object.Method.logic (method : Object.Method) (args : Anoma.Logic.Args method.AppData) : Bool :=
  let publicData : args.data.PublicData := args.data.publicData
  let argsData : method.Args := args.data.args
  let selfObj := @Object.fromResource _ args.data.rawPublicData publicData args.self
  let createdObjects := method.created selfObj argsData
  Logic.checkResourceData [selfObj] args.consumed
    && Logic.checkResourceData createdObjects args.created
    && method.extraLogic selfObj argsData

def Object.Method.action (method : Object.Method) (self : Object) (args : method.Args) : Anoma.Action :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let consumedObjects := [self]
  let consumedResources := List.map Object.toResource consumedObjects
  let createdObjects := method.created self args
  let createdResources := List.map Object.toResource createdObjects
  @Action.create _ method.rawArgs args
    consumedObjects createdObjects
    consumedResources createdResources

def Object.Method.transaction (method : Object.Method) (self : Object) (args : method.Args) (currentRoot : Anoma.CommitmentRoot) : Anoma.Transaction :=
  let action := method.action self args
  { roots := [currentRoot],
    actions := [action],
    -- TODO: set deltaProof properly
    deltaProof := "" }

end Goose
