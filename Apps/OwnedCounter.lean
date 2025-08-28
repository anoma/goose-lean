import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib

structure OwnedCounter where
  count : Nat
  owner : PublicKey
  deriving Inhabited, Repr, BEq

namespace OwnedCounter

instance hasTypeRep : TypeRep OwnedCounter where
  rep := Rep.atomic "OwnedCounter"

inductive Methods where
  | Incr : Methods
  | Transfer : Methods
  deriving DecidableEq, Fintype, Repr

inductive Constructors where
  | Zero : Constructors
  deriving DecidableEq, Fintype, Repr

inductive Destructors where
  | Ten : Destructors
  deriving DecidableEq, Fintype, Repr

inductive Classes where
  | OwnedCounter : Classes
  deriving DecidableEq, FinEnum, Repr

open AVM

def clab : Class.Label where
  name := "OwnedCounter"
  PrivateFields := ⟨OwnedCounter⟩
  MethodId := Methods
  MethodArgs := fun
    | Methods.Incr => ⟨Nat⟩
    | Methods.Transfer => ⟨PublicKey⟩
  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Zero => ⟨Unit⟩
  DestructorId := Destructors

def label : Ecosystem.Label where
  name := "OwnedCounterEcosystem"
  ClassId := Classes
  classLabel := fun
    | Classes.OwnedCounter => clab

def toObject (c : OwnedCounter) : ObjectData clab where
  quantity := 1
  privateFields := c

def fromObject (o : ObjectData clab) : OwnedCounter :=
  o.privateFields

instance instIsObject : IsObject OwnedCounter where
  label := label
  classId := Classes.OwnedCounter
  toObject := OwnedCounter.toObject
  fromObject := OwnedCounter.fromObject

def newCounter (owner : PublicKey) : OwnedCounter where
  count := 0
  owner

def incrementBy (step : Nat) (c : OwnedCounter) : OwnedCounter :=
  {c with count := c.count + step}

def counterConstructor : @Class.Constructor label Classes.OwnedCounter Constructors.Zero := defConstructor
  (body := fun (_noArgs : Unit) => Program.return fun _ => newCounter default)

def counterIncr : @Class.Method label Classes.OwnedCounter Methods.Incr := defMethod OwnedCounter
  (body := fun (self : OwnedCounter) (step : Nat) => Program.return fun _ => self.incrementBy step)

def counterTransfer : @Class.Method label Classes.OwnedCounter Methods.Transfer := defMethod OwnedCounter
  (body := fun (self : OwnedCounter) (newOwner : PublicKey) =>
    Program.return fun _ => {self with owner := newOwner : OwnedCounter})

/-- We only allow the counter to be destroyed if its count is at least 10 -/
def counterDestroy : @Class.Destructor label Classes.OwnedCounter Destructors.Ten := defDestructor
  (body := fun (_ : OwnedCounter) () => Program.return fun _ => ())
  (invariant := fun (self : OwnedCounter) () => self.count >= 10)

def counterClass : @Class label Classes.OwnedCounter where
  constructors := fun
    | Constructors.Zero => counterConstructor
  methods := fun
    | Methods.Incr => counterIncr
    | Methods.Transfer => counterTransfer
  destructors := fun
    | Destructors.Ten => counterDestroy
