import Goose
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib

structure Counter where
  count : Nat

namespace Counter

inductive Methods where
  | Incr : Methods
  deriving DecidableEq, Fintype, Repr

inductive Constructors where
  | Zero : Constructors
  deriving DecidableEq, Fintype, Repr

deriving instance Inhabited for Counter

open Goose

def sig : Signature where
  priv := {PrivateFields := Nat}
  pub := {PublicFields := Unit,
          MethodId := Methods
          MethodArgs := fun
            | Methods.Incr => Nat
          repMethodArgs := fun
            | Methods.Incr => inferInstance
          beqMethodArgs := fun
            | Methods.Incr => inferInstance
          ConstructorId := Constructors
          ConstructorArgs := fun
            | Constructors.Zero => Unit
          repConstructorArgs := fun
            | Constructors.Zero => inferInstance
          beqConstructorArgs := fun
            | Constructors.Zero => inferInstance}
  classLabel := "UniversalCounter"

def toObject (c : Counter) : Object sig where
  publicFields := Unit.unit
  quantity := 1
  privateFields := c.count

def fromObject (o : Object sig) : Option Counter := do
  guard (o.quantity == 1)
  some (Counter.mk (o.privateFields))

instance instCounterIsObject : IsObject Counter where
  sig := sig
  toObject := Counter.toObject
  fromObject := Counter.fromObject
  roundTrip : Counter.fromObject ∘ Counter.toObject = some := by rfl

def newCounter : Counter where
  count := 0

def incrementBy (step : Nat) (c : Counter) : Counter :=
  {c with count := c.count + step}

def counterConstructor : @Class.Constructor sig Constructors.Zero := defConstructor
  (created := fun (_noArgs : Unit) => newCounter)
  (extraLogic := fun (_noArgs : Unit) => True)

def counterIncr : @Class.Method sig Methods.Incr := defMethod
  (created := fun (self : Counter) (step : Nat) => [self.incrementBy step])
  (extraLogic := fun _ _ => True)

def counterClass : Class sig where
  constructors := fun
    | Constructors.Zero => counterConstructor
  methods := fun
    | Methods.Incr => counterIncr
  extraLogic _ _ := True
