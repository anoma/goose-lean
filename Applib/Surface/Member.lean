import AVM
import Applib.Surface.Program

namespace Applib

open AVM

macro "noConstructors" : term => `(fun x => Empty.elim x)
macro "noDestructors" : term => `(fun x => Empty.elim x)
macro "noMethods" : term => `(fun x => Empty.elim x)

def unsigned
  {lab : Ecosystem.Label}
  {SignatureId : Type}
  : MessageData lab → SignatureId → Signature := fun msg _ => Signature.sign msg PrivateKey.universal

def defMethod (cl : Type) [i : IsObject cl] {methodId : i.classId.label.MethodId}
 (body : (self : cl) → methodId.Args.type → Program i.label.toScope cl)
 (invariant : (msg : Message i.label) → (self : cl) → (args : methodId.Args.type) → Bool := fun _ _ _ => true)
 : Class.Method i.classId methodId where
    invariant (msg : Message i.label) (self : Object i.classId) (args : methodId.Args.type) :=
      let self' : cl := i.fromObject self.data
      invariant msg self' args
    body (self : Object i.classId) (args : methodId.Args.type) :=
      let self' := i.fromObject self.data
      let prog := body self' args
      prog.map (fun obj => {self with data := i.toObject obj})
        |>.toAVM

def defConstructor {cl : Type} [i : IsObject cl] {constrId : i.classId.label.ConstructorId}
 (body : constrId.Args.type → Program i.label.toScope cl)
 (invariant : (msg : Message i.label) → (args : constrId.Args.type) → Bool := fun _ _ => true)
 : Class.Constructor i.classId constrId where
    invariant (msg : Message i.label) (args : constrId.Args.type) := invariant msg args
    body (args : constrId.Args.type) := body args |>.map i.toObject |>.toAVM

def defDestructor {cl : Type} [i : IsObject cl] {destructorId : i.classId.label.DestructorId}
 (body : (self : cl) → destructorId.Args.type → Program i.label.toScope PUnit := fun _ _ => Program.return ())
 (invariant : (msg : Message i.label) → (self : cl) -> (args : destructorId.Args.type) → Bool := fun _ _ _ => true)
 : Class.Destructor i.classId destructorId where
    invariant (msg : Message i.label) (self : Object i.classId) (args : destructorId.Args.type) :=
      let self' := i.fromObject self.data
      invariant msg self' args
    body (self : Object i.classId) (args : destructorId.Args.type) :=
      body (i.fromObject self.data) args |>.toAVM
