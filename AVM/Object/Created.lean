import Anoma
import AVM.Class.Label
import AVM.Object

namespace AVM

structure CreatedObject where
  {label : Class.Label}
  uid : Anoma.ObjectId
  data : ObjectData label
  ephemeral : Bool
  /-- A unique random value used for the nonce of the balancing dummy ephemeral
    resource in the same compliance unit. -/
  rand : Nat

def CreatedObject.fromSomeObject (obj : SomeObject) (ephemeral : Bool) (rand : Nat) : CreatedObject :=
  { uid := obj.object.uid,
    data := obj.object.data,
    ephemeral,
    rand }
