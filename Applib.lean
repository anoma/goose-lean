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
 (body : (self : cl) -> methodId.Args -> List AnObject)
 (invariant : (self : cl) -> methodId.Args -> Bool := fun _ _ => True)
 : Class.Method methodId where
    invariant (self : Object i.lab) (args : methodId.Args) :=
      match i.fromObject self with
        | none => False
        | (some self') => invariant self' args
    created (self : Object i.lab) (args : methodId.Args) :=
      match i.fromObject self with
        | none => []
        | (some self') => List.map AnObject.toSomeObject (body self' args)

def defConstructor {cl : Type} [i : IsObject cl] {constrId : i.lab.ConstructorId}
 (body : constrId.Args -> cl)
 (invariant : constrId.Args -> Bool := fun _ => True)
 : Class.Constructor constrId where
    invariant (args : constrId.Args) := invariant args
    created (args : constrId.Args) := i.toObject (body args)
