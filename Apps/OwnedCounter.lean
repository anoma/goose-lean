import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib

structure Counter where
  count : Nat
  key : Anoma.NullifierKeyCommitment

namespace Counter

inductive Methods where
  | Incr : Methods
  deriving DecidableEq, Fintype, Repr

inductive Constructors where
  | Zero : Constructors
  deriving DecidableEq, Fintype, Repr

deriving instance Inhabited for Counter

open AVM

def lab : Class.Label where
  priv := {PrivateFields := Nat}
  pub := {PublicFields := Unit}
  MethodId := Methods
  MethodArgsTypes := fun
    | Methods.Incr => {type := Nat}
  ConstructorId := Constructors
  ConstructorArgsTypes := fun
    | Constructors.Zero => {type := Unit}
  name := "UniversalCounter"

def toObject (c : Counter) : Object lab where
  publicFields := Unit.unit
  quantity := 1
  privateFields := c.count
  nullifierKeyCommitment := c.key

def fromObject (o : Object lab) : Option Counter := do
  guard (o.quantity == 1)
  let key <- o.nullifierKeyCommitment
  some (Counter.mk (o.privateFields) key)

instance hasIsObject : IsObject Counter where
  lab := lab
  toObject := Counter.toObject
  fromObject := Counter.fromObject
  roundTrip : Counter.fromObject ∘ Counter.toObject = some := by rfl

def newCounter (key : Anoma.NullifierKeyCommitment) : Counter where
  count := 0
  key

def incrementBy (step : Nat) (c : Counter) : Counter :=
  {c with count := c.count + step}

def counterConstructor : @Class.Constructor lab Constructors.Zero := defConstructor
  (body := fun (_noArgs : Unit) => newCounter default)
  (invariant := fun (_noArgs : Unit) => True)

def counterIncr : @Class.Method lab Methods.Incr := defMethod
  (body := fun (self : Counter) (step : Nat) => [self.incrementBy step])
  (invariant := fun _ _ => True)

def counterClass : Class lab where
  constructors := fun
    | Constructors.Zero => counterConstructor
  methods := fun
    | Methods.Incr => counterIncr
  invariant _ _ := True
