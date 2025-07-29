/-
A kudos app which allows users to mint kudos and exchange them only with 1-to-1
swap intents.
-/

import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib

/-- Public name of someone -/
abbrev PublicIden := Nat

structure Kudos where
  quantity : Nat
  originator : PublicIden
  owner : PublicIden
  deriving DecidableEq, Inhabited

namespace Kudos

inductive Constructors where
  | Mint : Constructors
  deriving DecidableEq, Fintype, Repr

structure MintArgs where
  owner : PublicIden
  quantity : Nat
  deriving BEq

instance MintArgs.hasTypeRep : TypeRep MintArgs where
  rep := Rep.atomic "MintArgs"

structure SwapArgs where
  wantOriginator : PublicIden
  deriving DecidableEq

instance SwapArgs.hasTypeRep : TypeRep SwapArgs where
  rep := Rep.atomic "SwapArgs"

open AVM

def swapLabel : Intent.Label where
  Args := ⟨SwapArgs⟩
  name := "Kudos.Swap"

def kudosLabel : Class.Label where
  name := "Kudos"
  PrivateFields := ⟨PublicIden × PublicIden⟩

  MethodId := Empty
  MethodArgs := fun x => nomatch x

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Mint => ⟨MintArgs⟩

  intentLabels := {swapLabel}

def toObject (c : Kudos) : Object kudosLabel where
  quantity := c.quantity
  privateFields := (c.originator, c.owner)

def fromObject (o : Object kudosLabel) : Option Kudos := do
  some { owner := o.privateFields.2,
         quantity := o.quantity
         originator := o.privateFields.1 }

instance hasIsObject : IsObject Kudos where
  label := kudosLabel
  toObject := Kudos.toObject
  fromObject := Kudos.fromObject
  roundTrip : Kudos.fromObject ∘ Kudos.toObject = some := by rfl

def kudosMint : @Class.Constructor kudosLabel Constructors.Mint := defConstructor
  (body := fun (args : MintArgs) => { quantity := args.quantity
                                      owner := args.owner
                                      originator := args.owner : Kudos})

def kudosSwap : Intent swapLabel where
  condition (args : SwapArgs) (provided : List SomeObject) (received : List SomeObject) : Bool :=
    match provided, received with
    | [providedObj], [receivedObj] =>
      let try providedObj' : Object kudosLabel := tryCast providedObj.object
      let try receivedObj' : Object kudosLabel := tryCast receivedObj.object
      let try providedKudos : Kudos := Kudos.fromObject providedObj'
      let try receivedKudos : Kudos := Kudos.fromObject receivedObj'
      providedKudos.owner == receivedKudos.owner
      && receivedKudos.originator == args.wantOriginator
    | _, _ => false
