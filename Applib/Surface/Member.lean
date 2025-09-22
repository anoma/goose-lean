import AVM
import Applib.Surface.Program

namespace Applib

open AVM

macro "noConstructors" : term => `(fun x => Empty.elim x)
macro "noDestructors" : term => `(fun x => Empty.elim x)
macro "noMethods" : term => `(fun x => Empty.elim x)

def noSignatures
  {Args SignatureId : Type}
  {args : Args}
  : SignatureId → Signature args := fun _ => Signature.sign args PrivateKey.universal

def defMethod (cl : Type) [i : IsObject cl] {methodId : i.classId.label.MethodId}
 (body : (self : cl) → methodId.Args.type → Program i.label cl)
 (invariant : (self : cl) → (args : methodId.Args.type) → methodId.Signatures args → Bool := fun _ _ _ => true)
 : Class.Method i.classId methodId where
    invariant (self : Object i.classId) (args : methodId.Args.type) :=
      let self' : cl := i.fromObject self.data
      invariant self' args
    body (self : Object i.classId) (args : methodId.Args.type) :=
      let self' := i.fromObject self.data
      let prog := body self' args
      prog.map (fun obj => {self with data := i.toObject obj})
        |>.toAVM

def defConstructor {cl : Type} [i : IsObject cl] {constrId : i.classId.label.ConstructorId}
 (body : constrId.Args.type → Program i.label cl)
 (invariant : constrId.Args.type → Bool := fun _ => true)
 : Class.Constructor i.classId constrId where
    invariant (args : constrId.Args.type) := invariant args
    body (args : constrId.Args.type) := body args |>.map i.toObject |>.toAVM

def defDestructor {cl : Type} [i : IsObject cl] {destructorId : i.classId.label.DestructorId}
 (body : (self : cl) → destructorId.Args.type → Program i.label PUnit := fun _ _ => Program.return ())
 (invariant : (self : cl) -> (args : destructorId.Args.type) → destructorId.Signatures args → Bool := fun _ _ _ => true)
 : Class.Destructor i.classId destructorId where
    invariant (self : Object i.classId) (args : destructorId.Args.type) (signatures : destructorId.Signatures args) :=
      let self' := i.fromObject self.data
      invariant self' args signatures
    body (self : Object i.classId) (args : destructorId.Args.type) :=
      body (i.fromObject self.data) args |>.toAVM
