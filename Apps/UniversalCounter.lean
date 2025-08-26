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

inductive Classes where
  | Counter : Classes
  deriving DecidableEq, FinEnum, Repr

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

def label : Ecosystem.Label where
  name := "UniversalCounterEcosystem"
  ClassId := Classes
  classLabel := fun
    | Classes.Counter => clab

def toObject (c : Counter) : ObjectData clab where
  quantity := 1
  privateFields := c.count

def fromObject (o : ObjectData clab) : Counter :=
  Counter.mk o.privateFields

instance instIsObject : IsObject Counter where
  label := label
  classId := Classes.Counter
  toObject := Counter.toObject
  fromObject := Counter.fromObject

def newCounter : Counter where
  count := 0

def incrementBy (step : Nat) (c : Counter) : Counter :=
  {c with count := c.count + step}

def counterConstructor : @Class.Constructor label Classes.Counter Constructors.Zero := defConstructor
  (body := fun (_noArgs : Unit) => Program.return fun _ => newCounter)

def counterIncr : @Class.Method label Classes.Counter Methods.Incr := defMethod
  (body := fun (self : Counter) (step : Nat) => Program.return fun _ => self.incrementBy step)

def counterClass : @Class label Classes.Counter where
  constructors := fun
    | Constructors.Zero => counterConstructor
  methods := fun
    | Methods.Incr => counterIncr
  destructors := noDestructors
