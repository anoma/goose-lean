import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Applib.Surface.Program.Syntax

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

inductive MultiMethods where
  | Mutual : MultiMethods
  deriving Repr, DecidableEq, FinEnum

namespace MultiMethods

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

end MultiMethods

open MultiMethods
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
  name := "UniversalCounter Ecosystem"
  ClassId := Unit
  classLabel _ := clab
  MultiMethodId := MultiMethods
  MultiMethodObjectArgClass _ := .unit
  MultiMethodObjectArgNames := fun
    | MultiMethods.Mutual => Mutual.ArgNames

def toObject (c : Counter) : @ObjectData label .unit where
  quantity := 1
  privateFields := c.count

def fromObject (o : @ObjectData label .unit) : Counter :=
  Counter.mk o.privateFields

instance instIsObject : @IsObject Counter where
  label := label
  classId := Unit.unit
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

def mutualMethod : @Ecosystem.MultiMethod label .Mutual where
  invariant _ _ := true
  body selves (_args : Unit) :=
    let prog : _ := ⟪
         let c1 : Counter := selves .Counter1 |>.data |> fromObject
         let c2 : Counter := selves .Counter2 |>.data |> fromObject
         let c3 : Counter := { count := c1.count + c2.count : Counter }
         return {
           assembled := {
             withOldUid _ _ := none
             withNewUid := [c3.toObject.toSomeObjectData]
             : Assembled _ }
           argDeconstruction := fun
             | .Counter1 => .Disassembled
             | .Counter2 => .Disassembled
            : @MultiMethodResult label .Mutual
         }⟫.toAVM
    prog

def counterEcosystem : Ecosystem label where
  classes _ := counterClass
  multiMethods := fun
    | .Mutual => mutualMethod
