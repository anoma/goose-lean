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

def label : Ecosystem.Label := Ecosystem.Label.singleton clab

def toObject (c : Counter) : ObjectData clab where
  quantity := 1
  privateFields := c.count

def fromObject (o : ObjectData clab) : Counter :=
  Counter.mk o.privateFields

instance instIsObject : IsObject Counter where
  label := label
  classId := PUnit.unit
  toObject := Counter.toObject
  fromObject := Counter.fromObject

def newCounter : Counter where
  count := 0

def incrementBy (step : Nat) (c : Counter) : Counter :=
  {c with count := c.count + step}

def counterConstructor : @Class.Constructor label .unit Constructors.Zero := defConstructor
  (body := fun (_noArgs : Unit) => ⟪return newCounter⟫)

def counterIncr : @Class.Method label .unit Methods.Incr := defMethod
  (body := fun (self : Counter) (step : Nat) => ⟪return self.incrementBy step⟫)

def counterClass : @Class label .unit where
  constructors := fun
    | Constructors.Zero => counterConstructor
  methods := fun
    | Methods.Incr => counterIncr
  destructors := noDestructors
