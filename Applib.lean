import Goose

namespace Applib

open Goose

class IsObject (s : Type) where
  sig : Signature
  toObject : s -> Object sig
  fromObject : Object sig -> Option s
  roundTrip : fromObject ∘ toObject = some

structure AnObject where
  {ty : Type}
  [isObject : IsObject ty]
  obj : ty

def AnObject.toSomeObject (g : AnObject) : SomeObject :=
  let i : IsObject g.ty := g.isObject
  (i.toObject g.obj).toSomeObject

instance {ty : Type} [IsObject ty] : CoeHead ty AnObject where
  coe (obj : ty) := {obj}

def defMethod {cl Args : Type} [TypeRep Args] [BEq Args] [i : IsObject cl]
 -- TODO rename created to body
 (created : (self : cl) -> Args -> List AnObject)
 (extraLogic : (self : cl) -> Args -> Bool := fun _ _ => True)
 : Class.Method i.sig where
    Args := Args
    extraLogic (self : Object i.sig) (args : Args) :=
      match i.fromObject self with
        | none => False
        | (some self') => extraLogic self' args
    created (self : Object i.sig) (args : Args) :=
      match i.fromObject self with
        | none => []
        | (some self') => List.map AnObject.toSomeObject (created self' args)

def defConstructor {cl Args : Type} [TypeRep Args] [BEq Args] [i : IsObject cl]
 (created : Args -> cl)
 -- TODO rename extraLogic to extraConstraints
 (extraLogic : Args -> Bool)
 : Class.Constructor i.sig where
    Args := Args
    extraLogic (args : Args) := extraLogic args
    created (args : Args) := i.toObject (created args)
