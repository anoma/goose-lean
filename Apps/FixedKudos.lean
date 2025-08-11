/-
A kudos app which allows users to mint kudos and exchange them only with 1-to-1
swap intents.
-/

import AVM
import Applib
import Std.Data.HashSet.Lemmas
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib
open AVM

namespace FixedKudos

/-- Public name of someone -/
abbrev PublicIden := Nat

structure Kudos where
  quantity : Nat
  originator : PublicIden
  owner : PublicIden
  deriving DecidableEq, Inhabited

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

def Kudos.toObject (c : Kudos) : Object kudosLabel where
  quantity := c.quantity
  privateFields := (c.originator, c.owner)

def Kudos.fromObject (o : Object kudosLabel) : Option Kudos := do
  some { owner := o.privateFields.2,
         quantity := o.quantity
         originator := o.privateFields.1 }

instance hasIsObject : IsObject Kudos where
  label := kudosLabel
  toObject := Kudos.toObject
  fromObject := Kudos.fromObject

def kudosMint : @Class.Constructor kudosLabel Constructors.Mint := defConstructor
  (body := fun (args : MintArgs) => { quantity := args.quantity
                                      owner := args.owner
                                      originator := args.owner : Kudos})

def kudosSwap : Intent swapLabel :=
  defIntent swapLabel fun args =>
  [{ providedArgs := [⟨Kudos⟩]
     receivedArgs := [⟨Kudos⟩]
     condition := fun
       | (provided, PUnit.unit), (received, PUnit.unit) =>
         provided.owner == received.owner
         && received.originator == args.wantOriginator }]

def eco : Ecosystem.Label := Ecosystem.Label.singleton kudosLabel

def kudosClass : @Class eco PUnit.unit where
  constructors := fun
    | Constructors.Mint => kudosMint
  methods := noMethods
  intents := fun swapLabel h =>
      let h' : FixedKudos.swapLabel = swapLabel := by
          unfold Ecosystem.Label.ClassId.label eco Ecosystem.Label.singleton kudosLabel at h
          simp at h; assumption
      h' ▸ kudosSwap
  destructors := noDestructors
