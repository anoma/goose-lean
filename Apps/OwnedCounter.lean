import AVM
import Applib

open Applib

structure OwnedCounter where
  count : Nat
  owner : PublicKey
  deriving Inhabited, Repr, BEq, Hashable

namespace OwnedCounter

instance hasTypeRep : TypeRep OwnedCounter where
  rep := Rep.atomic "OwnedCounter"

inductive Methods where
  | Incr : Methods
  | Transfer : Methods
  deriving DecidableEq, FinEnum, Repr

namespace Methods

inductive Transfer.SignatureId : Type where
  | owner
  deriving DecidableEq, FinEnum

inductive Incr.SignatureId : Type where
  | owner
  deriving DecidableEq, FinEnum

abbrev SignatureId : Methods → Type
 | .Incr => Incr.SignatureId
 | .Transfer => Transfer.SignatureId

end Methods

inductive Constructors where
  | Zero : Constructors
  deriving DecidableEq, FinEnum, Repr

inductive Destructors where
  | Ten : Destructors
  deriving DecidableEq, FinEnum, Repr

namespace Destructors

inductive Ten.SignatureId : Type where
  | owner
 deriving DecidableEq, FinEnum

abbrev SignatureId : Destructors → Type
 | .Ten => Ten.SignatureId

end Destructors

open AVM

def clab : Class.Label where
  name := "OwnedCounter"
  PrivateFields := ⟨OwnedCounter⟩
  MethodId := Methods
  MethodArgs := fun
    | Methods.Incr => ⟨Nat⟩
    | Methods.Transfer => ⟨PublicKey⟩
  MethodSignatureId := Methods.SignatureId
  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Zero => ⟨Unit⟩
  DestructorId := Destructors
  DestructorSignatureId := Destructors.SignatureId

def label : Ecosystem.Label := Ecosystem.Label.singleton clab

def toObject (c : OwnedCounter) : @ObjectData label .unit where
  quantity := 1
  privateFields := c

def fromObject (o : @ObjectData label .unit) : OwnedCounter :=
  o.privateFields

instance instIsObject : IsObject OwnedCounter where
  label := label
  classId := .unit
  isObjectOf :=
    { toObject := OwnedCounter.toObject
      fromObject := OwnedCounter.fromObject }

def newCounter (owner : PublicKey) : OwnedCounter where
  count := 0
  owner

def incrementBy (step : Nat) (c : OwnedCounter) : OwnedCounter :=
  {c with count := c.count + step}

def counterConstructor : @Class.Constructor label .unit Constructors.Zero := defConstructor
  (body := fun (_noArgs : Unit) => ⟪return newCounter default⟫)

def counterIncr : @Class.Method label .unit Methods.Incr := defMethod OwnedCounter
  (body := fun (self : OwnedCounter) (step : Nat) => ⟪return self.incrementBy step⟫)
  (invariant := fun (self : OwnedCounter) (_step : Nat) signatures =>
    checkSignature (signatures .owner) self.owner)

def counterTransfer : @Class.Method label .unit Methods.Transfer := defMethod OwnedCounter
  (body := fun (self : OwnedCounter) (newOwner : PublicKey) =>
    ⟪return {self with owner := newOwner : OwnedCounter}⟫)
  (invariant := fun (self : OwnedCounter) (_newOwner : PublicKey) signatures =>
    checkSignature (signatures .owner) self.owner)

/-- We only allow the counter to be destroyed if its count is at least 10 -/
def counterDestroy : @Class.Destructor label .unit Destructors.Ten := defDestructor
  (invariant := fun (self : OwnedCounter) () signatures =>
    checkSignature (signatures .owner) self.owner
    && self.count >= 10)

def counterClass : @Class label .unit where
  constructors := fun
    | Constructors.Zero => counterConstructor
  methods := fun
    | Methods.Incr => counterIncr
    | Methods.Transfer => counterTransfer
  destructors := fun
    | Destructors.Ten => counterDestroy
