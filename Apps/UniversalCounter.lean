import AVM
import Applib
import Anoma
import Applib.Surface.Program.Syntax

open Applib

structure Counter where
  count : Nat
  deriving Inhabited, Repr

namespace Counter

inductive Methods where
  | Incr : Methods
  deriving DecidableEq, FinEnum, Repr

inductive Constructors where
  | Zero : Constructors
  deriving DecidableEq, FinEnum, Repr

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

def mergeMethod : @Ecosystem.MultiMethod label .Merge :=
  defMultiMethod label MultiMethods.Merge
    (argsInfo := fun
      | .Counter1 => { type := Counter, isObjectOf := Counter.instIsObjectOf }
      | .Counter2 => { type := Counter, isObjectOf := Counter.instIsObjectOf } )
    (body := fun selves (_args : Unit) => ⟪
      let c1 : Counter := selves .Counter1
      let c2 : Counter := selves .Counter2
      let c3 : Counter := { count := c1.count + c2.count : Counter }
      return {
        assembled := {
          withOldUid _ _ := none
          withNewUid := [c3] }
        argDeconstruction := fun
          | .Counter1 => .Disassembled
          | .Counter2 => .Disassembled
      }
    ⟫)

def counterEcosystem : Ecosystem label where
  classes _ := counterClass
  multiMethods := fun
    | .Merge => mergeMethod

def example1 : Applib.Program label.toScope Unit := ⟪
  -- log s!"create"
  c1 := create Counter Counter.Constructors.Zero ()
  -- c1' := fetch c1
  -- log s!"hi {c1'.count}"
  return .unit
⟫

def example2 (rx ry : Reference Counter) : Applib.Program label.toScope Unit := ⟪
  let selves :
      @Ecosystem.Label.MultiMethodId.SelvesReferences label
      Counter.MultiMethods.Merge := fun
        | .Counter1 => { type := Counter
                         isObjectOf := Counter.instIsObjectOf
                         ref := rx }
        | .Counter2 => { type := Counter
                         isObjectOf := Counter.instIsObjectOf
                         ref := ry }
  multiCall[ .unit ] Counter.MultiMethods.Merge selves .unit
⟫

def scope : AVM.Scope label.toScope := counterEcosystem.toScope

end Counter

def runProgram {α} (prog : Applib.Program Counter.label.toScope α) : IO Unit :=
  let p : Anoma.Program := prog.map (fun _ => Unit.unit) |>.toAVM.compile Counter.scope
  p.run ∅

def main : IO Unit := runProgram Counter.example1
