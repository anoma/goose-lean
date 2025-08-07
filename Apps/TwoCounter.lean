import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib
open AVM

namespace TwoCounterApp

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

def lab : Class.Label where
  name := "UniversalCounter"
  PrivateFields := ⟨Nat⟩

  SubObjects := noSubObjects

  MethodId := Methods
  MethodArgs := fun
    | Methods.Incr => ⟨Nat⟩

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Zero => ⟨Unit⟩

  intentLabels := ∅

def toObject (c : Counter) : Object lab where
  quantity := 1
  privateFields := c.count
  subObjects := noSubObjects

def fromObject (o : Object lab) : Option Counter := do
  guard (o.quantity == 1)
  some (Counter.mk o.privateFields)

instance instIsObject : IsObject Counter where
  label := lab
  toObject
  fromObject
  roundTrip : fromObject ∘ toObject = some := by rfl

def new : Counter where
  count := 0

def incrementBy (step : Nat) (c : Counter) : Counter :=
  {c with count := c.count + step}

def constructor : @Class.Constructor lab Constructors.Zero := defConstructor
  (body := fun (_noArgs : Unit) => Counter.new)

def incr : @Class.Method lab Methods.Incr := defMethod
  (body := fun (self : Counter) (step : Nat) => [self.incrementBy step])

end Counter

structure TwoCounter where
  c1 : Reference Counter.lab
  c2 : Reference Counter.lab
  deriving Repr

namespace TwoCounter

inductive Constructors where
  | Zero : Constructors
  deriving DecidableEq, Fintype, Repr

def lab : Class.Label where
  name := "TwoCounter"
  PrivateFields := ⟨SomeReference × SomeReference⟩

  SubObjects := noSubObjects

  MethodId := Empty
  MethodArgs := noMethods

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Zero => ⟨SomeReference × SomeReference⟩

  intentLabels := ∅

def new (c1 c2 : Reference Counter.lab) : TwoCounter where
  c1
  c2

def toObject (c : TwoCounter) : Object lab where
  quantity := 1
  privateFields := ⟨c.c1.forget, c.c2.forget⟩
  subObjects := noSubObjects

def fromObject (o : Object lab) : Option TwoCounter := do
  guard (o.quantity == 1)
  some (TwoCounter.mk o.privateFields.1.coerce o.privateFields.2.coerce)

instance instIsObject : IsObject TwoCounter where
  label := lab
  toObject := toObject
  fromObject := fromObject
  roundTrip : fromObject ∘ toObject = some := by
    apply funext; intro x
    unfold Function.comp toObject fromObject; simp
    rw [forget_coerce x.c1, forget_coerce x.c2]

def constructor : @Class.Constructor lab Constructors.Zero := defConstructor
  (body := fun (args : SomeReference × SomeReference) =>
   { c1 := args.1.coerce
     c2 := args.2.coerce
     : TwoCounter })

end TwoCounter

namespace TwoCounterEco

inductive Classes where
  | Counter
  | TwoCounter
  deriving BEq, DecidableEq, Repr, FinEnum

def lab : Ecosystem.Label where
  name := "Two Counter Ecosystem"
  ClassId := Classes
  classLabel := fun
    | .Counter => Counter.lab
    | .TwoCounter => TwoCounter.lab
  FunctionObjectArgClass := noFunctions

def counterClass : @Class lab .Counter where
  constructors := fun
    | Counter.Constructors.Zero => Counter.constructor
  methods := fun
    | Counter.Methods.Incr => Counter.incr
  destructors := noDestructors
  intents := noIntents lab Counter.lab

def twoCounterClass : @Class lab .TwoCounter where
  constructors := fun
    | TwoCounter.Constructors.Zero => TwoCounter.constructor
  methods := noMethods
  destructors := noDestructors
  intents := noIntents lab TwoCounter.lab

def ecosystem : Ecosystem lab where
  classes := fun
    | .Counter => counterClass
    | .TwoCounter => twoCounterClass
  functions := noFunctions

-- A program that receives two Counter reference as arguments and returns a reference to a TwoCounter
def mkTwoCounter : Program (Vector.ofFn (n := 2) fun
   | 0 => .Reference Counter.lab
   | 1 => .Reference Counter.lab)
   (.Reference TwoCounter.lab) :=
  Program.allocate TwoCounter.lab
  <| Program.store (.var ⟨0, _⟩) TwoCounter.new

def mainProgram : TopProgram (.SomeType ⟨Unit⟩) :=
  Program.allocate Counter.lab
  <| Program.store (.var ⟨0, _⟩) Counter.new.toObject
  <| Program.allocate Counter.lab
  <| Program.store (.var ⟨0, _⟩) Counter.new.toObject
  <| Program.noop
