
import Goose.Object

namespace Goose

structure Class.Constructor where
  /-- The type of constructor arguments. -/
  Args : Type
  [rawArgs : Anoma.Raw Args]
  /-- Extra constructor logic. It is combined with auto-generated constructor
      logic to create the complete constructor logic. -/
  extraLogic : Args → Bool
  /-- Objects created in the constructor call. -/
  created : Args → Object

structure Class.Method where
  /-- The type of method arguments (excluding `self`). -/
  Args : Type
  [rawArgs : Anoma.Raw Args]
  classLabel : String
  /-- Extra method logic. It is combined with auto-generated method logic to
      create the complete method logic. -/
  extraLogic : (self : Object) → Args → Bool
  /-- Objects created in the method call. -/
  created : (self : Object) → Args → List Object

/-- A class member is a method or a constructor. -/
inductive Class.Member where
  | constructor (constr : Class.Constructor) : Class.Member
  | method (method : Class.Method) : Class.Member

/-- The appData associated with a member call consists of the
    self object's public fields and the member arguments. -/
structure Class.Member.AppData (Args : Type u) where
  PublicFields : Type
  [rawPublicFields : Anoma.Raw PublicFields]
  publicFields : PublicFields
  args : Args

def Class.Method.AppData (method : Class.Method) :=
  Member.AppData method.Args

def Class.Constructor.AppData (constr : Class.Constructor) :=
  Member.AppData constr.Args

instance Class.Member.AppData.RawInstance {Args} [Anoma.Raw Args] : Anoma.Raw (Class.Member.AppData Args) where
  raw appData := appData.rawPublicFields.raw appData.publicFields ++ ":::" ++ Anoma.Raw.raw appData.args

def Class.Member.appData {Args} (self : Object) (args : Args) : Class.Member.AppData Args :=
  { PublicFields := self.PublicFields,
    rawPublicFields := self.rawPublicFields,
    publicFields := self.publicFields,
    args }

end Goose
