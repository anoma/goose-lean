import AVM
import Applib.Program

namespace Applib

open AVM

macro "noConstructors" : term => `(fun x => Empty.elim x)
macro "noDestructors" : term => `(fun x => Empty.elim x)
macro "noMethods" : term => `(fun x => Empty.elim x)

class IsObject (s : Type) where
  label : Ecosystem.Label
  classId : label.ClassId
  toObject : s → ObjectData classId.label
  fromObject : ObjectData classId.label → s
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

def defMethod (cl : Type) [i : IsObject cl] {methodId : i.classId.label.MethodId}
 (body : (self : cl) → methodId.Args.type → Program i.label cl)
 (invariant : (self : cl) → methodId.Args.type → Bool := fun _ _ => true)
 : Class.Method i.classId methodId where
    invariant (self : Object i.classId.label) (args : methodId.Args.type) :=
      let self' : cl := i.fromObject self.data
      invariant self' args
    body (self : Object i.classId.label) (args : methodId.Args.type) :=
      let self' := i.fromObject self.data
      let prog := body self' args
      prog.map fun obj => {self with data := i.toObject obj}

def defConstructor {cl : Type} [i : IsObject cl] {constrId : i.classId.label.ConstructorId}
 (body : constrId.Args.type → Program i.label cl)
 (invariant : constrId.Args.type → Bool := fun _ => true)
 : Class.Constructor i.classId constrId where
    invariant (args : constrId.Args.type) := invariant args
    body (args : constrId.Args.type) := body args |>.map i.toObject

def defDestructor {cl : Type} [i : IsObject cl] {destructorId : i.classId.label.DestructorId}
 (body : (self : cl) → destructorId.Args.type → Program i.label PUnit)
 (invariant : (self : cl) -> destructorId.Args.type → Bool := fun _ _ => true)
 : Class.Destructor i.classId destructorId where
    invariant (self : Object i.classId.label) (args : destructorId.Args.type) :=
      let self' := i.fromObject self.data
      invariant self' args
    body (self : Object i.classId.label) (args : destructorId.Args.type) :=
      body (i.fromObject self.data) args
