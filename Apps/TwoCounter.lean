import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib
open AVM

namespace TwoCounterApp

inductive Classes where
  | Counter : Classes
  | TwoCounter : Classes
  deriving DecidableEq, FinEnum, Repr

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

  MethodId := Methods
  MethodArgs := fun
    | Methods.Incr => ⟨Nat⟩

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Zero => ⟨Unit⟩

def toObject (c : Counter) : ObjectData lab where
  quantity := 1
  privateFields := c.count

def fromObject (o : ObjectData lab) : Counter :=
  Counter.mk o.privateFields

def new : Counter where
  count := 0

def incrementBy (step : Nat) (c : Counter) : Counter :=
  {c with count := c.count + step}

end Counter

structure TwoCounter where
  c1 : ObjectId
  c2 : ObjectId
  deriving Repr

namespace TwoCounter

inductive Constructors where
  | Zero : Constructors
  deriving DecidableEq, Fintype, Repr

inductive Methods where
  | IncrementBoth : Methods
  deriving DecidableEq, Fintype, Repr

def lab : Class.Label where
  name := "TwoCounter"
  PrivateFields := ⟨ObjectId × ObjectId⟩

  MethodId := Methods
  MethodArgs := fun
    | Methods.IncrementBoth => ⟨Nat⟩

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Zero => ⟨ObjectId × ObjectId⟩

def new (c1 c2 : ObjectId) : TwoCounter where
  c1
  c2

def toObject (c : TwoCounter) : ObjectData lab where
  quantity := 1
  privateFields := ⟨c.c1, c.c2⟩

def fromObject (o : ObjectData lab) : TwoCounter :=
  TwoCounter.mk o.privateFields.1 o.privateFields.2

end TwoCounter

namespace Eco

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

end Eco

namespace Counter

instance instIsObject : IsObject Counter where
  label := Eco.lab
  classId := Eco.Classes.Counter
  toObject := Counter.toObject
  fromObject := Counter.fromObject

def constructor : @Class.Constructor Eco.lab Eco.Classes.Counter Constructors.Zero := defConstructor
  (body := fun (_noArgs : Unit) => Program.return fun _ => Counter.new)

def incr : @Class.Method Eco.lab Eco.Classes.Counter Methods.Incr := defMethod
  (body := fun (self : Counter) (step : Nat) =>
    Program.return fun _ => self.incrementBy step)

end Counter

namespace TwoCounter

instance instIsObject : IsObject TwoCounter where
  label := Eco.lab
  classId := Eco.Classes.TwoCounter
  toObject
  fromObject

def constructor : @Class.Constructor Eco.lab Eco.Classes.TwoCounter Constructors.Zero := defConstructor
  (body := fun (args : ObjectId × ObjectId) =>
    Program.return fun _ =>
      { c1 := args.1
        c2 := args.2
        : TwoCounter })

def incrementBoth : @Class.Method Eco.lab Eco.Classes.TwoCounter Methods.IncrementBoth := defMethod
  (body := fun (self : TwoCounter) (n : Nat) =>
    Program.fetch Counter (fun _ => self.c1) <|
    Program.fetch Counter (fun _ => self.c2) <|
    Program.call Eco.Classes.Counter Counter.Methods.Incr (fun _ => self.c1)
      (fun ⟨c1, ⟨c2, ()⟩⟩ =>
        c2.count * n + c1.count) <|
    Program.call Eco.Classes.Counter Counter.Methods.Incr (fun _ => self.c2)
      (fun ⟨c1, ⟨c2, ()⟩⟩ =>
        c1.count * n + c2.count) <|
    Program.return fun _ => self)

end TwoCounter

namespace Eco

def counterClass : @Class lab .Counter where
  constructors := fun
    | Counter.Constructors.Zero => Counter.constructor
  methods := fun
    | Counter.Methods.Incr => Counter.incr
  destructors := noDestructors

def twoCounterClass : @Class lab .TwoCounter where
  constructors := fun
    | TwoCounter.Constructors.Zero => TwoCounter.constructor
  methods := fun
    | TwoCounter.Methods.IncrementBoth => TwoCounter.incrementBoth
  destructors := noDestructors

def ecosystem : Ecosystem lab where
  classes := fun
    | .Counter => counterClass
    | .TwoCounter => twoCounterClass
