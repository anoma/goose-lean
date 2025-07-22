import AVM

namespace Applib

open AVM

macro "noIntents" lab:ident clab:ident : term => `(fun _ h => by simp [$lab:ident, Ecosystem.Label.ClassId.label, Ecosystem.Label.singleton, $clab:ident] at h)
macro "noDestructors" : term => `(fun x => Empty.elim x)
macro "noFunctions" : term => `(fun x => Empty.elim x)
macro "noMethods" : term => `(fun x => Empty.elim x)

class IsObject (s : Type) where
  lab : Class.Label
  toObject : s → Object lab
  fromObject : Object lab → Option s
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

def defMethod (cl : Type) [i : IsObject cl] {methodId : i.lab.MethodId}
 (body : (self : cl) → methodId.Args.type → List AnObject)
 (invariant : (self : cl) → methodId.Args.type → Bool := fun _ _ => true)
 : Class.Method methodId where
    invariant (self : Object i.lab) (args : methodId.Args.type) :=
      let try self' := i.fromObject self
      invariant self' args
    created (self : Object i.lab) (args : methodId.Args.type) :=
      let try self' := i.fromObject self
      List.map AnObject.toSomeObject (body self' args)

def defConstructor {cl : Type} [i : IsObject cl] {constrId : i.lab.ConstructorId}
 (body : constrId.Args.type → cl)
 (invariant : constrId.Args.type → Bool := fun _ => true)
 : Class.Constructor constrId where
    invariant (args : constrId.Args.type) := invariant args
    created (args : constrId.Args.type) := i.toObject (body args)

def defDestructor {cl : Type} [i : IsObject cl] {destructorId : i.lab.DestructorId}
 (invariant : (self : cl) -> destructorId.Args.type → Bool := fun _ _ => true)
 : Class.Destructor destructorId where
    invariant (self : Object i.lab) (args : destructorId.Args.type) :=
    let try self' := i.fromObject self
    invariant self' args
