
import Anoma.Raw

namespace Goose

structure Object where
  PrivateData : Type
  PublicData : Type
  [rawPrivateData : Anoma.Raw PrivateData]
  [rawPublicData : Anoma.Raw PublicData]
  quantity : Nat
  -- privateData goes into the value field of the resource
  privateData : PrivateData
  -- publicData goes into the appData field of the action
  publicData : PublicData
  classLabel : String

structure Object.Constructor.Result where
  created : Object
  extraLogic : Bool

structure Object.Constructor where
  Args : Type
  [rawArgs : Anoma.Raw Args]
  run : Args → Object.Constructor.Result

structure Object.Method.Result where
  consumed : Object -- self. This field is redundant, but maybe convenient (?)
  created : List Object
  extraLogic : Bool

structure Object.Method where
  Args : Type
  [rawArgs : Anoma.Raw Args]
  classLabel : String
  run : (self : Object) → Args -> Object.Method.Result

structure Object.Method.AppData (method : Object.Method) where
  Data : Type
  methodData : Data
  args : method.Args


-- TODO: change this to a structure
-- The appData associated with an object in a method call consists of object's
-- public data and the method arguments.
-- def Object.Method.AppData (method : Object.Method) : Type 1 :=
--   (α : Type) × α × method.Args

end Goose
