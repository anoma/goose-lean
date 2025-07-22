import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib

structure Counter where
  count : Nat
  deriving Inhabited, Repr

namespace Counter

inductive Methods where
  | Incr : Methods
  deriving DecidableEq, Fintype, Repr

inductive Constructors where
  | Zero : Constructors
  deriving DecidableEq, Fintype, Repr

open AVM

def clab : Class.Label where
  name := "UniversalCounter"
  PrivateFields := ⟨Nat⟩

  MethodId := Methods
  MethodArgs := fun
    | Methods.Incr => ⟨Nat⟩

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Zero => ⟨Unit⟩

  intentLabels := ∅

def lab : Ecosystem.Label := Ecosystem.Label.singleton clab

def toObject (c : Counter) : Object clab where
  quantity := 1
  privateFields := c.count
  nullifierKeyCommitment := none

def fromObject (o : Object clab) : Option Counter := do
  guard (o.quantity == 1)
  some (Counter.mk (o.privateFields))

instance hasIsObject : IsObject Counter where
  lab := clab
  toObject := Counter.toObject
  fromObject := Counter.fromObject
  roundTrip : Counter.fromObject ∘ Counter.toObject = some := by rfl

def newCounter : Counter where
  count := 0

def incrementBy (step : Nat) (c : Counter) : Counter :=
  {c with count := c.count + step}

def counterConstructor : @Class.Constructor clab Constructors.Zero := defConstructor
  (body := fun (_noArgs : Unit) => newCounter)

def counterIncr : @Class.Method clab Methods.Incr := defMethod
  (body := fun (self : Counter) (step : Nat) => [self.incrementBy step])

def counterClass : @Class lab UUnit.unit where
  constructors := fun
    | Constructors.Zero => counterConstructor
  methods := fun
    | Methods.Incr => counterIncr
  destructors := noDestructors
  intents := noIntents lab clab

def counterEcosystem : Ecosystem lab where
  classes := fun _ => counterClass
  functions := noFunctions
