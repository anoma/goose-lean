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
  deriving Inhabited, Repr, BEq

instance Counter.HasTypeRep : TypeRep Counter where
  rep := Rep.atomic "TwoCounter.Counter"

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
  c1 : Reference Counter
  c2 : Reference Counter

namespace TwoCounter

inductive Constructors where
  | Zero : Constructors
  deriving DecidableEq, Fintype, Repr

inductive Methods where
  | IncrementBoth : Methods
  deriving DecidableEq, Fintype, Repr

def lab : Class.Label where
  name := "TwoCounter"
  PrivateFields := ⟨Reference Counter × Reference Counter⟩

  MethodId := Methods
  MethodArgs := fun
    | Methods.IncrementBoth => ⟨Nat⟩

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Zero => ⟨Reference Counter × Reference Counter⟩

def new (c1 c2 : Reference Counter) : TwoCounter where
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
  (body := fun (_noArgs : Unit) => ⟪return Counter.new⟫)

def incr : @Class.Method Eco.lab Eco.Classes.Counter Methods.Incr := defMethod
  (body := fun (self : Counter) (step : Nat) =>
    ⟪return self.incrementBy step⟫)

end Counter

namespace TwoCounter

instance instIsObject : IsObject TwoCounter where
  label := Eco.lab
  classId := Eco.Classes.TwoCounter
  toObject
  fromObject

def constructor : @Class.Constructor Eco.lab Eco.Classes.TwoCounter Constructors.Zero := defConstructor
  (body := fun (args : Reference Counter × Reference Counter) => ⟪
    return
      { c1 := args.1
        c2 := args.2
        : TwoCounter }
  ⟫)

def incrementBoth : @Class.Method Eco.lab Eco.Classes.TwoCounter Methods.IncrementBoth := defMethod
  (body := fun (self : TwoCounter) (n : Nat) => ⟪
    c1 := fetch self.c1
    c2 := fetch self.c2
    call Counter Counter.Methods.Incr self.c1 (c2.count * n + c1.count)
    call Counter Counter.Methods.Incr self.c2 (c1.count * n + c2.count)
    return self
  ⟫)

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
