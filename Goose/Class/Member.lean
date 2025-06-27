import Goose.Object
import Goose.Signature

namespace Goose

structure Class.Constructor (sig : Signature) where
  /-- The type of constructor arguments. -/
  Args : Type
  [rawArgs : Anoma.Raw Args]
  /-- Extra constructor logic. It is combined with auto-generated constructor
      logic to create the complete constructor logic. -/
  extraLogic : Args → Bool
  /-- Objects created in the constructor call. -/
  created : Args → Object sig

structure Class.Method (sig : Signature) where
  /-- The type of method arguments (excluding `self`). -/
  Args : Type
  [rawArgs : Anoma.Raw Args]
  classLabel : String
  /-- Extra method logic. It is combined with auto-generated method logic to
      create the complete method logic. -/
  extraLogic : (self : Object sig) → Args → Bool
  /-- Objects created in the method call. -/
  created : (self : Object sig) → Args → List SomeObject

/-- A class member is a method or a constructor. -/
inductive Class.Member (sig : Signature) where
  | constructor (constr : Class.Constructor sig) : Class.Member sig
  | method (method : Class.Method sig) : Class.Member sig

/-- The appData associated with a member call consists of the
    self object's public fields and the member arguments. -/
structure Class.Member.AppData (pub : Public) (Args : Type u) where
  publicFields : pub.PublicFields
  args : Args

structure Class.Member.SomeAppData (Args : Type u) where
  {pub : Public}
  appData : Class.Member.AppData pub Args

def Class.Member.AppData.toSomeAppData {pub : Public} {Args : Type u}
  (appData : Class.Member.AppData pub Args)
  : Class.Member.SomeAppData Args
  := {appData}

def Class.Method.AppData (sig : Signature) (method : Class.Method sig) :=
  Member.AppData sig.pub method.Args

def Class.Constructor.AppData {sig : Signature} (constr : Class.Constructor sig) :=
  Member.AppData sig.pub constr.Args

instance Class.Member.AppData.RawInstance (pub : Public) {Args : Type u} [Anoma.Raw Args]
   : Anoma.Raw (Class.Member.AppData pub Args) where
  raw appData := pub.rawPublicFields.raw appData.publicFields ++ ":::" ++ Anoma.Raw.raw appData.args
  cooked := panic! "cooked"

def Class.Member.appData {Args : Type u} (sig : Signature) (self : Object sig) (args : Args)
  : Class.Member.AppData sig.pub Args :=
  {
    publicFields := self.publicFields,
    args }

def Class.Member.someAppData {Args : Type u} (self : SomeObject) (args : Args)
  : Class.Member.SomeAppData Args :=
    (Class.Member.appData self.sig self.object args).toSomeAppData

end Goose
