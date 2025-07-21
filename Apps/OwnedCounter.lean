import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib

structure OwnedCounter where
  count : Nat
  /-- Only someone who knows the NullifierKey can increment the counter -/
  key : Anoma.NullifierKeyCommitment
  deriving Inhabited, Repr

namespace OwnedCounter

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
  PrivateFields := ⟨Nat⟩
  MethodId := Methods
  MethodArgs := fun
    | Methods.Incr => ⟨Nat⟩
    | Methods.Transfer => ⟨Anoma.NullifierKeyCommitment⟩
  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Zero => ⟨Unit⟩
  DestructorId := Destructors

def lab : Ecosystem.Label := Ecosystem.Label.singleton clab

def toObject (c : OwnedCounter) : Object clab where
  quantity := 1
  privateFields := c.count
  nullifierKeyCommitment := c.key

def fromObject (o : Object clab) : Option OwnedCounter := do
  guard (o.quantity == 1)
  let key ← o.nullifierKeyCommitment
  some (OwnedCounter.mk (o.privateFields) key)

instance hasIsObject : IsObject OwnedCounter where
  lab := clab
  toObject := OwnedCounter.toObject
  fromObject := OwnedCounter.fromObject
  roundTrip : OwnedCounter.fromObject ∘ OwnedCounter.toObject = some := by rfl

def newCounter (key : Anoma.NullifierKeyCommitment) : OwnedCounter where
  count := 0
  key

def incrementBy (step : Nat) (c : OwnedCounter) : OwnedCounter :=
  {c with count := c.count + step}

def counterConstructor : @Class.Constructor clab Constructors.Zero := defConstructor
  (body := fun (_noArgs : Unit) => newCounter default)

def counterIncr : @Class.Method clab Methods.Incr := defMethod OwnedCounter
  (body := fun (self : OwnedCounter) (step : Nat) => [self.incrementBy step])

def counterTransfer : @Class.Method clab Methods.Transfer := defMethod OwnedCounter
  (body := fun (self : OwnedCounter) (newOwner : Anoma.NullifierKeyCommitment) => [{self with key := newOwner : OwnedCounter}])

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

def counterEcosystem : Ecosystem lab where
  classes := fun _ => counterClass
  intents := noIntents
  functions := noFunctions
