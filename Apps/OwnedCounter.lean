import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib

structure OwnedCounter where
  count : Nat
  /-- Only someone who knows the NullifierKey can increment the counter -/
  key : Anoma.NullifierKeyCommitment

namespace OwnedCounter

inductive Methods where
  | Incr : Methods
  | Transfer : Methods
  deriving DecidableEq, Fintype, Repr

inductive Constructors where
  | Zero : Constructors
  deriving DecidableEq, Fintype, Repr

deriving instance Inhabited for OwnedCounter

open AVM

def lab : Class.Label where
  PrivateFields := ⟨Nat⟩
  PublicFields := ⟨Unit⟩
  MethodId := Methods
  MethodArgs := fun
    | Methods.Incr => ⟨Nat⟩
    | Methods.Transfer => ⟨Anoma.NullifierKeyCommitment⟩
  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Zero => ⟨Unit⟩
  name := "OwnedCounter"

def toObject (c : OwnedCounter) : Object lab where
  publicFields := Unit.unit
  quantity := 1
  privateFields := c.count
  nullifierKeyCommitment := c.key

def fromObject (o : Object lab) : Option OwnedCounter := do
  guard (o.quantity == 1)
  let key <- o.nullifierKeyCommitment
  some (OwnedCounter.mk (o.privateFields) key)

instance hasIsObject : IsObject OwnedCounter where
  lab := lab
  toObject := OwnedCounter.toObject
  fromObject := OwnedCounter.fromObject
  roundTrip : OwnedCounter.fromObject ∘ OwnedCounter.toObject = some := by rfl

def newCounter (key : Anoma.NullifierKeyCommitment) : OwnedCounter where
  count := 0
  key

def incrementBy (step : Nat) (c : OwnedCounter) : OwnedCounter :=
  {c with count := c.count + step}

def counterConstructor : @Class.Constructor lab Constructors.Zero := defConstructor
  (body := fun (_noArgs : Unit) => newCounter default)

def counterIncr : @Class.Method lab Methods.Incr := defMethod OwnedCounter
  (body := fun (self : OwnedCounter) (step : Nat) => [self.incrementBy step])

def counterTransfer : @Class.Method lab Methods.Transfer := defMethod OwnedCounter
  (body := fun (self : OwnedCounter) (newOwner : Anoma.NullifierKeyCommitment) => [{self with key := newOwner : OwnedCounter}])

def counterClass : Class lab where
  constructors := fun
    | Constructors.Zero => counterConstructor
  methods := fun
    | Methods.Incr => counterIncr
    | Methods.Transfer => counterTransfer
