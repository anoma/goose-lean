import Goose
import Anoma.Raw

namespace Applib

open Goose

class IsObject (s : Type) where
  sig : Signature
  toObject : s -> Object sig
  fromObject : Object sig -> Option s
  roundTrip : fromObject ∘ toObject = some

-- TODO better name
structure GObject where
  {ty : Type}
  [isObject : IsObject ty]
  obj : ty

def GObject.toSomeObject (g : GObject) : SomeObject :=
  let i : IsObject g.ty := g.isObject
  (i.toObject g.obj).toSomeObject

instance {ty : Type} [IsObject ty] : CoeHead ty GObject where
  coe (obj : ty) := {obj}

def defMethod {cl Args : Type} [Anoma.Raw Args] [i : IsObject cl]
 (created : (self : cl) -> Args -> List GObject)
 (extraLogic : (self : cl) -> Args -> Bool := fun _ _ => True)
 : Class.Method i.sig where
    Args := Args
    classLabel := i.sig.classLabel
    extraLogic (self : Object i.sig) (args : Args) :=
      match i.fromObject self with
        | none => False
        | (some self') => extraLogic self' args
    created (self : Object i.sig) (args : Args) :=
      match i.fromObject self with
        | none => []
        | (some self') => List.map GObject.toSomeObject (created self' args)

def defConstructor {cl Args : Type} [Anoma.Raw Args] [i : IsObject cl]
 (created : Args -> cl)
 (extraLogic : Args -> Bool)
 : Class.Constructor i.sig where
    Args := Args
    extraLogic (args : Args) := extraLogic args
    created (args : Args) := i.toObject (created args)
