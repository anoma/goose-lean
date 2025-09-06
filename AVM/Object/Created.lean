import Anoma
import AVM.Class.Label
import AVM.Object

namespace AVM

structure CreatedObject where
  {label : Class.Label}
  uid : Anoma.ObjectId
  data : ObjectData label
  ephemeral : Bool

def CreatedObject.fromSomeObjectData (data : SomeObjectData) (uid : ObjectId) (ephemeral : Bool) : CreatedObject :=
  { uid,
    data := data.data,
    ephemeral }

def CreatedObject.fromSomeObject (obj : SomeObject) (ephemeral : Bool) : CreatedObject :=
  { uid := obj.object.uid,
    data := obj.object.data,
    ephemeral }

def CreatedObject.toResource (c : CreatedObject) (nonce : Anoma.Nonce) : Anoma.Resource :=
  let obj : Object c.label := {uid := c.uid, nonce, data := c.data}
  Object.toResource obj (ephemeral := c.ephemeral)
