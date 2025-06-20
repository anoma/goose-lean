
import Goose.Object
import Anoma

namespace Goose

def Object.toResource (obj : Object) (ephemeral := false) (nonce := 0) (nkCommitment := "") : Anoma.Resource :=
  { Val := obj.PrivateData
    rawVal := obj.rawPrivateData
    label := obj.classLabel
    quantity := obj.quantity
    value := obj.privateData
    ephemeral := ephemeral
    nonce := nonce
    nullifierKeyCommitment := nkCommitment }

def Object.fromResource {Data} [Anoma.Raw Data] (publicData : Data) (res : Anoma.Resource) : Object :=
  { PrivateData := res.Val
    PublicData := Data
    rawPrivateData := res.rawVal
    quantity := res.quantity
    privateData := res.value
    publicData := publicData
    classLabel := res.label }

def methodLogic (method : Object.Method) (args : Anoma.Logic.Args method.AppData) : Bool :=
  -- TODO: this is wrong, we should use publicData instead of argsData
  let argsData : method.Args := args.data.args
  let self : Object := @Object.fromResource _ method.rawArgs argsData args.self
  let result := method.run self argsData
  let createdObjects := result.created
  createdObjects.length == args.created.length
    && List.and (List.zipWith resourceDataEq createdObjects args.created)
    && result.extraLogic
  where
    resourceDataEq (obj : Object) (res : Anoma.Resource) : Bool :=
      @Anoma.rawEq _ _ res.rawVal obj.rawPrivateData res.value obj.privateData
        && res.label == obj.classLabel

def constructorAction (constr : Object.Constructor) (args : constr.Args) : Anoma.Action :=
  let res := constr.run args
  let eph : Anoma.Resource := Object.toResource (ephemeral := true) res.created
  let new : Object := res.created
  let newRes : Anoma.Resource := Object.toResource res.created
  -- TODO I don't fully understand appData
  let appData : Std.HashMap Anoma.RawTag new.PublicData :=
    Std.HashMap.emptyWithCapacity.insert (Anoma.RawTag.fromResource (isConsumed := false) newRes) new.publicData
  {
    Data := new.PublicData,
    rawData := new.rawPublicData,
    consumed := [Anoma.RootedNullifiableResource.Transparent.fromResource eph],
    created := [Object.toResource res.created],
    appData }

def methodAction (method : Object.Method) (self : Object) (args : method.Args) : Anoma.Action :=
  let selfResource := Object.toResource self
  let createdResources := List.map Object.toResource (method.run self args).created
  let appData : Std.HashMap Anoma.RawTag self.PublicData :=
    Std.HashMap.emptyWithCapacity.insert (Anoma.RawTag.fromResource (isConsumed := true) selfResource) self.publicData
    --  |>.insertMany (List.map (fun res => Anoma.Tag.fromResource false res) createdResources)
  { Data := self.PublicData,
    rawData := self.rawPublicData,
    consumed := [Anoma.RootedNullifiableResource.Transparent.fromResource selfResource],
    created := createdResources,
    appData }

def methodTransaction (method : Object.Method) (self : Object) (args : method.Args) : Anoma.Transaction :=
  sorry

end Goose
