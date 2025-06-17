
namespace Goose

structure Object where
  PrivateData : Type
  PublicData : Type
  quantity : Nat
  -- privateData goes into the value field of the resource
  privateData : PrivateData
  -- publicData goes into the appData field of the action
  publicData : PublicData
  classLabel : String

structure Object.Constructor where
  Args : Type
  extraLogic : Args → Bool
  created : Args → Object

structure Object.Method where
  Args : Type
  classLabel : String
  extraLogic : Object → Args → Bool
  created : Object → Args → List Object

end Goose
