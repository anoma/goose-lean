import Goose
import Applib

open Applib

namespace Counter

open Goose

structure Counter where
  count : Nat

deriving instance Inhabited for Counter

def sig : Signature where
  priv := {PrivateFields := Nat}
  pub := {PublicFields := Unit}
  classLabel := "UniversalCounter"

def Counter.toObject (c : Counter) : Object sig where
  publicFields := Unit.unit
  quantity := 1
  privateFields := c.count

def Counter.fromObject (o : Object sig) : Option Counter := do
  guard (o.quantity == 1)
  some (Counter.mk (o.privateFields))

instance instCounterIsObject : IsObject Counter where
  sig := sig
  toObject := Counter.toObject
  fromObject := Counter.fromObject
  roundTrip : Counter.fromObject ∘ Counter.toObject = some := by rfl

def newCounter : Counter where
  count := 0

def Counter.incrementBy (step : Nat) (c : Counter) : Counter :=
  {c with count := c.count + step}

def counterConstructor : Class.Constructor sig := defConstructor
  (created := fun (_noArgs : Unit) => newCounter)
  (extraLogic := fun (_noArgs : Unit) => True)

def counterIncr : Class.Method sig := defMethod
  (created := fun (self : Counter) (step : Nat) => [self.incrementBy step])
  (extraLogic := fun _ _ => True)

def counterClass : Class sig where
  constructors := [counterConstructor]
  methods := [counterIncr]
  extraLogic _ _ := True
