import AVM

namespace Applib

open AVM

class IsObject (s : Type) where
  lab : Class.Label
  toObject : s -> Object lab
  fromObject : Object lab -> Option s
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

def defMethod {cl : Type} [i : IsObject cl] {methodId : i.lab.MethodId}
 -- TODO rename created to body
 (created : (self : cl) -> methodId.Args -> List AnObject)
 (extraLogic : (self : cl) -> methodId.Args -> Bool := fun _ _ => True)
 : Class.Method methodId where
    extraLogic (self : Object i.lab) (args : methodId.Args) :=
      match i.fromObject self with
        | none => False
        | (some self') => extraLogic self' args
    created (self : Object i.lab) (args : methodId.Args) :=
      match i.fromObject self with
        | none => []
        | (some self') => List.map AnObject.toSomeObject (created self' args)

def defConstructor {cl : Type} [i : IsObject cl] {constrId : i.lab.ConstructorId}
 (created : constrId.Args -> cl)
 -- TODO rename extraLogic to extraConstraints
 (extraLogic : constrId.Args -> Bool)
 : Class.Constructor constrId where
    extraLogic (args : constrId.Args) := extraLogic args
    created (args : constrId.Args) := i.toObject (created args)
