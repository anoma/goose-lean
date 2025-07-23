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
  deriving DecidableEq, Fintype, Repr

namespace Functions

instance instFinEnum : FinEnum Functions :=
  FinEnum.ofList [Mutual]
  fun
  | Mutual => by simp

namespace Mutual

inductive ArgNames where
  | Counter1
  | Counter2
  deriving DecidableEq, Repr

export ArgNames (Counter1 Counter2)

instance ArgNames.instFinEnum : FinEnum ArgNames :=
  FinEnum.ofList [Counter1, Counter2]
  fun
  | Counter1 => by simp
  | Counter2 => by simp

end Mutual
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
  some (Counter.mk (o.privateFields))

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
  FunctionObjectArgClass {f : Functions} (_a : _) := match f with
   | Functions.Mutual => UUnit.unit
  objectArgNamesEnum (f : Functions) : FinEnum _ := match f with
   | Functions.Mutual => inferInstance

def counterClass : @Class lab UUnit.unit where
  constructors := fun
    | Constructors.Zero => counterConstructor
  methods := fun
    | Methods.Incr => counterIncr
  destructors := noDestructors
  intents := noIntents lab clab

def counterEcosystem : Ecosystem lab where
  classes := fun _ => counterClass
  functions := fun .Mutual =>
    let mergeArgsInfo (a : lab.FunctionObjectArgNames Mutual)
      : ObjectArgInfo lab Mutual a :=
      match a with
      | Mutual.Counter1 => { type := Counter }
      | Mutual.Counter2 => { type := Counter }

    defFunction lab Mutual
      (argsInfo := mergeArgsInfo)
      (body := fun counters _args =>
                let c1 := counters Mutual.Counter1
                let c2 := counters Mutual.Counter2
                {created := [incrementBy c2.count c1,
                             incrementBy c1.count c2]})
      (invariant := fun _counters _args => true)
