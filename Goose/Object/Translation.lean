
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

def methodLogic (method : Object.Method) (args : Anoma.Logic.Args method.Args) : Bool :=
  let self := @Object.fromResource _ method.rawArgs args.data args.self
  let createdObjects := method.created self args.data
  createdObjects.length == args.created.length
    && List.and (List.zipWith resourceDataEq createdObjects args.created)
    && method.extraLogic self args.data
  where
    resourceDataEq (obj : Object) (res : Anoma.Resource) : Bool :=
      @Anoma.rawEq _ _ res.rawVal obj.rawPrivateData res.value obj.privateData
        && res.label == obj.classLabel

def methodAction (method : Object.Method) (self : Object) (args : method.Args) : Anoma.Action :=
  sorry

def methodTransaction (method : Object.Method) (self : Object) (args : method.Args) : Anoma.Transaction :=
  sorry

end Goose
