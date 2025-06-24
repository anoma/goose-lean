
import Anoma.Raw

namespace Goose

/-- Represents a concrete object, translated into a resource. For class
    represetation (object description), see `Goose.Class`. -/
structure Object where
  PrivateData : Type
  PublicData : Type
  [rawPrivateData : Anoma.Raw PrivateData]
  [rawPublicData : Anoma.Raw PublicData]
  classLabel : String
  quantity : Nat
  /-- `privateData` goes into the `value` field of the resource -/
  privateData : PrivateData
  /-- `publicData` goes into the `appData` field of the action -/
  publicData : PublicData

structure Object.Constructor where
  /-- The type of constructor arguments. -/
  Args : Type
  [rawArgs : Anoma.Raw Args]
  /-- Extra constructor logic. It is combined with auto-generated constructor
      logic to create the complete constructor logic. -/
  extraLogic : Args → Bool
  /-- Objects created in the constructor call. -/
  created : Args → Object

structure Object.Method where
  /-- The type of method arguments (excluding `self`). -/
  Args : Type
  [rawArgs : Anoma.Raw Args]
  classLabel : String
  /-- Extra method logic. It is combined with auto-generated method logic to
      create the complete method logic. -/
  extraLogic : (self : Object) → Args → Bool
  /-- Objects created in the method call. -/
  created : (self : Object) → Args → List Object

/-- The appData associated with an object in a method or constructor call
     consists of the object's public data and the method arguments. -/
structure Object.AppData (Args : Type u) where
  PublicData : Type
  [rawPublicData : Anoma.Raw PublicData]
  publicData : PublicData
  args : Args

def Object.Method.AppData (method : Object.Method) :=
  Object.AppData method.Args

def Object.Constructor.AppData (constr : Object.Constructor) :=
  Object.AppData constr.Args

instance Object.AppData.RawInstance {Args} [Anoma.Raw Args] : Anoma.Raw (Object.AppData Args) where
  raw appData := appData.rawPublicData.raw appData.publicData ++ ":::" ++ Anoma.Raw.raw appData.args

end Goose
