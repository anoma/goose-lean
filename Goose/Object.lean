
import Anoma.Raw

namespace Goose

structure Object where
  PrivateData : Type
  PublicData : Type
  [rawPrivateData : Anoma.Raw PrivateData]
  [rawPublicData : Anoma.Raw PublicData]
  classLabel : String
  quantity : Nat
  -- privateData goes into the value field of the resource
  privateData : PrivateData
  -- publicData goes into the appData field of the action
  publicData : PublicData

structure Object.Constructor where
  Args : Type
  [rawArgs : Anoma.Raw Args]
  extraLogic : Args → Bool
  created : Args → Object

structure Object.Method where
  Args : Type
  [rawArgs : Anoma.Raw Args]
  classLabel : String
  extraLogic : Object → Args → Bool
  created : Object → Args → List Object

-- The appData associated with an object in a method call consists of object's
-- public data and the method arguments.
structure Object.Method.AppData (method : Object.Method) where
  PublicData : Type
  [rawPublicData : Anoma.Raw PublicData]
  publicData : PublicData
  args : method.Args

end Goose
