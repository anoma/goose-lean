import Goose
import Anoma.Raw

namespace Counter

open Goose

axiom error {A : Type u} (msg : String) : A

def clLabel : String := "UniversalCounter"

structure Counter where
  count : Nat

deriving instance Inhabited for Counter

def newCounter : Counter where
  count := 0

def sig : Signature where
  priv := {PrivateFields := Nat}
  pub := {PublicFields := Unit}
  classLabel := clLabel

def Counter.toObject (c : Counter) : Object sig where
  publicFields := Unit.unit
  quantity := 1
  privateFields := c.count

def Counter.fromObject (o : Object sig) : Option Counter := do
  guard (o.quantity == 1)
  some (Counter.mk (o.privateFields))

def Counter.fromObject! (self : Object sig) : Counter :=
  match Counter.fromObject self with
    | none => panic! "self is not a Counter object"
    | some c => c

def counterConstructor : Class.Constructor sig where
  Args := Unit
  extraLogic (_ : Unit) : Bool := True
  created (_ : Unit) : Object sig := newCounter.toObject

def counterIncr : Class.Method sig where
 Args := Nat
 classLabel := clLabel
 extraLogic (_self : Object sig) (_inc : Nat) : Bool := True
 created (self : Object sig) (step : Nat) : List SomeObject :=
   match Counter.fromObject self with
    | none => panic! "self is not a Counter object"
    | some n => [{n with count := n.count + step}.toObject.toSomeObject];

def counterClass : Class sig where
  constructors := [counterConstructor]
  methods := [counterIncr]
  extraLogic (_self : Object sig) (_args : Anoma.Logic.Args (Class.Member.AppData sig.pub Unit)) : Bool := True
