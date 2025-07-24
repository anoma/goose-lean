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

inductive Functions where
  | Mutual : Functions
  | Absorb : Functions
  deriving DecidableEq, Fintype, Repr, FinEnum

namespace Functions

namespace Mutual

inductive ArgNames where
  | Counter1
  | Counter2
  deriving DecidableEq, Repr, FinEnum

export ArgNames (Counter1 Counter2)

end Mutual

namespace Absorb

inductive ArgNames where
  | Absorbing
  | Absorbed
  deriving DecidableEq, Repr, FinEnum

export ArgNames (Absorbing Absorbed)

end Absorb

end Functions

open Functions
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

def toObject (c : Counter) : Object clab where
  quantity := 1
  privateFields := c.count

def fromObject (o : Object clab) : Option Counter := do
  guard (o.quantity == 1)
  some (Counter.mk o.privateFields)

instance instIsObject : IsObject Counter where
  label := clab
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

def lab : Ecosystem.Label where
  name := "UniversalCounter"
  ClassId := UUnit
  classLabel := fun _ => clab
  classId := fun _ => none -- FIXME
  FunctionId := Functions
  FunctionObjectArgNames : Functions → Type := fun
   | Functions.Mutual => Mutual.ArgNames
   | Functions.Absorb => Absorb.ArgNames
  objectArgNamesEnum (f : Functions) : FinEnum _ := by
    cases f <;> exact inferInstance
  objectArgNamesBEq (f : Functions) : BEq _ := by
    cases f <;> exact inferInstance
  FunctionObjectArgClass {f : Functions} (_a : _) := UUnit.unit

def counterClass : @Class lab UUnit.unit where
  constructors := fun
    | Constructors.Zero => counterConstructor
  methods := fun
    | Methods.Incr => counterIncr
  destructors := noDestructors
  intents := noIntents lab clab

def counterEcosystem : Ecosystem lab where
  classes := fun _ => counterClass
  functions (f : Functions) := match f with
    | .Mutual =>
      let mutualArgsInfo (a : lab.FunctionObjectArgNames Mutual)
      : ObjectArgInfo lab Mutual a :=
        { type := Counter }

      defFunction lab Mutual
        (argsInfo := mutualArgsInfo)
        (body := fun counters _args =>
                  let c1 := counters .Counter1
                  let c2 := counters .Counter2
                  {created := [incrementBy c2.count c1,
                               incrementBy c1.count c2]})
        (invariant := fun _counters _args => true)

    | .Absorb =>
      let AbsorbArgsInfo (a : lab.FunctionObjectArgNames Absorb)
      : ObjectArgInfo lab Absorb a :=
        { type := Counter }

      defFunction lab Absorb
        (argsInfo := AbsorbArgsInfo)
        (body := fun counters _args =>
                  let absorbed := counters .Absorbed
                  let absorbing := counters .Absorbing
                  {created := [incrementBy absorbed.count absorbing]
                   destroyed := [{anObject := absorbed}] })
        (invariant := fun _counters _args => true)
