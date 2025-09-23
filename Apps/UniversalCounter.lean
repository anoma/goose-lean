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
  | Merge : MultiMethods
  deriving Repr, DecidableEq, FinEnum

namespace MultiMethods

namespace Merge

inductive ArgNames where
  | Counter1
  | Counter2
  deriving DecidableEq, Repr, FinEnum

export ArgNames (Counter1 Counter2)

end Merge

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
    | MultiMethods.Merge => Merge.ArgNames

def toObject (c : Counter) : @ObjectData label .unit where
  quantity := 1
  privateFields := c.count

def fromObject (o : @ObjectData label .unit) : Counter :=
  Counter.mk o.privateFields

instance instIsObjectOf : @IsObjectOf label .unit Counter where
  toObject := Counter.toObject
  fromObject := Counter.fromObject

instance instIsObject : IsObject Counter where
  label := label
  classId := Unit.unit
  isObjectOf := inferInstance

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

def mergeMethod : @Ecosystem.MultiMethod label .Merge where
  invariant _ _ _ := true
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
            : @MultiMethodResult label .Merge
         }⟫.toAVM
    prog

def counterEcosystem : Ecosystem label where
  classes _ := counterClass
  multiMethods := fun
    | .Merge => mergeMethod

example (rx ry : Reference Counter) : Applib.Program label Unit := ⟪
  let selves :
      @Ecosystem.Label.MultiMethodId.SelvesReferences label
      Counter.MultiMethods.Merge := fun
        | .Counter1 => { type := Counter
                         isObjectOf := by
                           unfold label
                           infer_instance
                         ref := rx }
        | .Counter2 => { type := Counter
                         isObjectOf := by
                           unfold label
                           infer_instance
                         ref := ry }
  multiCall Counter.MultiMethods.Merge selves .unit noSignatures
⟫
