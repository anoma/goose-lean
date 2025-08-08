import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib

structure OwnedCounter where
  count : Nat
  owner : PublicKey
  deriving Inhabited, Repr, BEq

namespace OwnedCounter

instance hasTypeRep : TypeRep OwnedCounter where
  rep := Rep.atomic "OwnedCounter"

inductive Methods where
  | Incr : Methods
  | Transfer : Methods
  deriving DecidableEq, Fintype, Repr

inductive Constructors where
  | Zero : Constructors
  deriving DecidableEq, Fintype, Repr

inductive Destructors where
  | Ten : Destructors
  deriving DecidableEq, Fintype, Repr

open AVM

def clab : Class.Label where
  name := "OwnedCounter"
  PrivateFields := ⟨OwnedCounter⟩
  SubObjects := noSubObjects
  MethodId := Methods
  MethodArgs := fun
    | Methods.Incr => ⟨Nat⟩
    | Methods.Transfer => ⟨PublicKey⟩
  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Zero => ⟨Unit⟩
  DestructorId := Destructors
  intentLabels := ∅

def lab : Ecosystem.Label := Ecosystem.Label.singleton clab

def toObject (c : OwnedCounter) : Object clab where
  quantity := 1
  privateFields := c
  subObjects := noSubObjects

def fromObject (o : Object clab) : Option OwnedCounter := do
  guard (o.quantity == 1)
  some (o.privateFields)

instance instIsObject : IsObject OwnedCounter where
  label := clab
  toObject := OwnedCounter.toObject
  fromObject := OwnedCounter.fromObject
  roundTrip : OwnedCounter.fromObject ∘ OwnedCounter.toObject = some := by rfl

def newCounter (owner : PublicKey) : OwnedCounter where
  count := 0
  owner

def incrementBy (step : Nat) (c : OwnedCounter) : OwnedCounter :=
  {c with count := c.count + step}

def counterConstructor : @Class.Constructor clab Constructors.Zero := defConstructor
  (body := fun (_noArgs : Unit) => newCounter default)

def counterIncr : @Class.Method clab Methods.Incr := defMethod OwnedCounter
  (body := fun (self : OwnedCounter) (step : Nat) => [self.incrementBy step])

def counterTransfer : @Class.Method clab Methods.Transfer := defMethod OwnedCounter
  (body := fun (self : OwnedCounter) (newOwner : PublicKey) => [{self with owner := newOwner : OwnedCounter}])

/-- We only allow the counter to be destroyed if its count is at least 10 -/
def counterDestroy : @Class.Destructor clab Destructors.Ten := defDestructor
 (invariant := fun (self : OwnedCounter) (_ : UUnit) => self.count >= 10)

def counterClass : @Class lab .unit where
  constructors := fun
    | Constructors.Zero => counterConstructor
  methods := fun
    | Methods.Incr => counterIncr
    | Methods.Transfer => counterTransfer
  destructors := fun
    | Destructors.Ten => counterDestroy
  intents := noIntents lab clab

def counterEcosystem : Ecosystem lab where
  classes := fun _ => counterClass
  functions := noFunctions
