
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
  let argsData : method.Args := args.data.snd.snd
  let self := @Object.fromResource _ method.rawArgs argsData args.self
  let createdObjects := method.created self argsData
  createdObjects.length == args.created.length
    && List.and (List.zipWith resourceDataEq createdObjects args.created)
    && method.extraLogic self argsData
  where
    resourceDataEq (obj : Object) (res : Anoma.Resource) : Bool :=
      @Anoma.rawEq _ _ res.rawVal obj.rawPrivateData res.value obj.privateData
        && res.label == obj.classLabel

def methodAction (method : Object.Method) (self : Object) (args : method.Args) : Anoma.Action :=
  let selfResource := Object.toResource self
  let createdResources := List.map Object.toResource (method.created self args)
  let appData : Std.HashMap Anoma.Tag self.PublicData :=
    Std.HashMap.emptyWithCapacity.insert (Anoma.Tag.fromResource true selfResource) self.publicData
    --  |>.insertMany (List.map (fun res => Anoma.Tag.fromResource false res) createdResources)
  { Data := self.PublicData,
    rawData := self.rawPublicData,
    consumed := [selfResource],
    created := createdResources,
    appData }

def methodTransaction (method : Object.Method) (self : Object) (args : method.Args) : Anoma.Transaction :=
  sorry

end Goose
