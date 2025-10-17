import AVM
import Applib

open Applib
open AVM

namespace TwoCounterApp

inductive Classes where
  | Counter : Classes
  | TwoCounter : Classes
  deriving DecidableEq, FinEnum, Repr

structure Counter where
  count : Nat
  deriving Inhabited, Repr, BEq, Hashable

instance Counter.HasTypeRep : TypeRep Counter where
  rep := Rep.atomic "TwoCounter.Counter"

namespace Counter

inductive Methods where
  | Incr : Methods
  deriving DecidableEq, FinEnum, Repr

inductive Constructors where
  | Zero : Constructors
  deriving DecidableEq, FinEnum, Repr

def lab : Class.Label where
  name := "UniversalCounter"
  PrivateFields := ⟨Nat⟩

  MethodId := Methods
  MethodArgs := fun
    | Methods.Incr => ⟨Nat⟩

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Zero => ⟨Unit⟩

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
  deriving DecidableEq, FinEnum, Repr

inductive Methods where
  | IncrementBoth : Methods
  deriving DecidableEq, FinEnum, Repr

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

end TwoCounter

namespace Eco

inductive Classes where
  | Counter
  | TwoCounter
  deriving BEq, DecidableEq, Repr, FinEnum

def label : Ecosystem.Label where
  name := "Two Counter Ecosystem"
  ClassId := Classes
  classLabel := fun
    | .Counter => Counter.lab
    | .TwoCounter => TwoCounter.lab
  MultiMethodObjectArgClass {f : Empty} := f.elim

end Eco

namespace Counter

def toObject (c : Counter) : @ObjectData Eco.label .Counter where
  quantity := 1
  privateFields := c.count

def fromObject (o : @ObjectData Eco.label .Counter) : Counter :=
  Counter.mk o.privateFields

instance instIsObject : IsObject Counter where
  label := Eco.label
  classId := Eco.Classes.Counter
  isObjectOf :=
    { toObject := Counter.toObject
      fromObject := Counter.fromObject }

def constructor : @Class.Constructor Eco.label Eco.Classes.Counter Constructors.Zero := defConstructor
  (body := fun (_noArgs : Unit) => ⟪return Counter.new⟫)

def incr : @Class.Method Eco.label Eco.Classes.Counter Methods.Incr := defMethod
  (body := fun (self : Counter) (step : Nat) =>
    ⟪return self.incrementBy step⟫)

end Counter

namespace TwoCounter

def toObject (c : TwoCounter) : @ObjectData Eco.label .TwoCounter where
  quantity := 1
  privateFields := ⟨c.c1, c.c2⟩

def fromObject (o : @ObjectData Eco.label .TwoCounter) : TwoCounter :=
  TwoCounter.mk o.privateFields.1 o.privateFields.2

instance instIsObject : IsObject TwoCounter where
  label := Eco.label
  classId := Eco.Classes.TwoCounter
  isObjectOf :=
    { toObject
      fromObject }

def constructor : @Class.Constructor Eco.label Eco.Classes.TwoCounter Constructors.Zero := defConstructor
  (body := fun (args : Reference Counter × Reference Counter) => ⟪
    return
      { c1 := args.1
        c2 := args.2
        : TwoCounter }
  ⟫)

def incrementBoth : @Class.Method Eco.label Eco.Classes.TwoCounter Methods.IncrementBoth := defMethod
  (body := fun (self : TwoCounter) (n : Nat) => ⟪
    c1 := fetch self.c1
    c2 := fetch self.c2
    call Counter.Methods.Incr self.c1 (c2.count * n + c1.count)
    call Counter.Methods.Incr self.c2 (c1.count * n + c2.count)
    return self
  ⟫)

end TwoCounter

namespace Eco

def counterClass : @Class label .Counter where
  constructors := fun
    | Counter.Constructors.Zero => Counter.constructor
  methods := fun
    | Counter.Methods.Incr => Counter.incr
  destructors := noDestructors

def twoCounterClass : @Class label .TwoCounter where
  constructors := fun
    | TwoCounter.Constructors.Zero => TwoCounter.constructor
  methods := fun
    | TwoCounter.Methods.IncrementBoth => TwoCounter.incrementBoth
  destructors := noDestructors

def ecosystem : Ecosystem label where
  classes := fun
    | .Counter => counterClass
    | .TwoCounter => twoCounterClass
  multiMethods (f : Empty) := f.elim
