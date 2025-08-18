import AVM

namespace Applib

open AVM

macro "noConstructors" : term => `(fun x => Empty.elim x)
macro "noDestructors" : term => `(fun x => Empty.elim x)
macro "noMethods" : term => `(fun x => Empty.elim x)

class IsObject (s : Type) where
  label : Class.Label
  toObject : s → ObjectData label
  fromObject : ObjectData label → s
  round_trip : fromObject ∘ toObject = id := by rfl

structure AnObjectType : Type 1 where
  ty : Type
  [isObject : IsObject ty]

structure AnObject : Type 1 where
  {ty : Type}
  [isObject : IsObject ty]
  obj : ty

def IsObject.toAnObject {cl : Type} [i : IsObject cl] (o : cl) : AnObject := ⟨o⟩

def AnObject.toSomeObject (g : AnObject) : SomeObjectData :=
  let i : IsObject g.ty := g.isObject
  (i.toObject g.obj).toSomeObjectData

instance {ty : Type} [IsObject ty] : CoeHead ty AnObject where
  coe (obj : ty) := {obj}

def defMethod (cl : Type) [i : IsObject cl] {methodId : i.label.MethodId}
 (body : (self : cl) → methodId.Args.type → cl)
 (invariant : (self : cl) → methodId.Args.type → Bool := fun _ _ => true)
 : Class.Method methodId where
    invariant (self : Object i.label) (args : methodId.Args.type) :=
      let self' : cl := i.fromObject self.data
      invariant self' args
    created (self : Object i.label) (args : methodId.Args.type) :=
      let self' := i.fromObject self.data
      [{self with data := i.toObject (body self' args)}.toSomeObject]

def defConstructor {cl : Type} [i : IsObject cl] {constrId : i.label.ConstructorId}
 (body : constrId.Args.type → cl)
 (invariant : constrId.Args.type → Bool := fun _ => true)
 : Class.Constructor constrId where
    invariant (args : constrId.Args.type) := invariant args
    created (args : constrId.Args.type) := i.toObject (body args)

def defDestructor {cl : Type} [i : IsObject cl] {destructorId : i.label.DestructorId}
 (invariant : (self : cl) -> destructorId.Args.type → Bool := fun _ _ => true)
 : Class.Destructor destructorId where
    invariant (self : Object i.label) (args : destructorId.Args.type) :=
      let self' := i.fromObject self.data
      invariant self' args
