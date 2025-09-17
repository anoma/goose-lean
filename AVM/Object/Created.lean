import Anoma
import AVM.Class.Label
import AVM.Object
import AVM.Action.DummyResource

namespace AVM

structure CreatedObject : Type 1 where
  {label : Ecosystem.Label}
  {classId : label.ClassId}
  uid : Anoma.ObjectId
  data : ObjectData classId
  ephemeral : Bool
  /-- A unique random value used for the nonce of the balancing dummy ephemeral
    resource in the same compliance unit. -/
  rand : Nat

def CreatedObject.fromSomeObject (obj : SomeObject) (ephemeral : Bool) (rand : Nat) : CreatedObject :=
  { uid := obj.object.uid
    classId := obj.classId
    data := obj.object.data
    ephemeral
    rand }
