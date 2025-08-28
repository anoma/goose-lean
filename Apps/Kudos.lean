import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib

/-- Kudos API Summary: -/
/- 1. Definition of *kudos token*: A kudos token has three parameters: -/
/-    1.1. The quantity -/
/-    1.2. The originator: The public key of the user that minted this token -/
/-    1.3. The owner: The public key of the user that owns this token -/
/- The following operations are supported: -/
/- 1. Minting: Any user with public key K can mint any quantity of tokens with originator = owner = K -/
/- 2. Transfer: The onwer of a kudos token can transfer it to another user -/
/- 3. Burn: The owner of a kudos token can destroy it if themself is the originator of the token -/

structure KudosData where
  originator : PublicKey
  owner : PublicKey
  deriving DecidableEq, Inhabited

structure Kudos extends KudosData where
  quantity : Nat
  deriving DecidableEq, Inhabited

namespace Kudos

inductive Methods where
  | Transfer : Methods
  deriving DecidableEq, Fintype, Repr

inductive Constructors where
  | Mint : Constructors
  deriving DecidableEq, Fintype, Repr

inductive Destructors where
  | Burn : Destructors
  deriving DecidableEq, Fintype, Repr

inductive Classes where
  | Kudos : Classes
  deriving DecidableEq, FinEnum, Repr

open AVM

instance KudosData.hasTypeRep : TypeRep KudosData where
  rep := Rep.atomic "KudosData"

instance hasTypeRep : TypeRep Kudos where
  rep := Rep.atomic "Kudos"

structure MintArgs where
  key : PrivateKey
  originator : PublicKey
  quantity : Nat
  deriving BEq

instance MintArgs.hasTypeRep : TypeRep MintArgs where
  rep := Rep.atomic "MintArgs"

structure TransferArgs where
  newOwner : PublicKey
  deriving DecidableEq

instance TransferArgs.hasTypeRep : TypeRep TransferArgs where
  rep := Rep.atomic "TransferArgs"

def clab : Class.Label where
  name := "Kudos"
  PrivateFields := ⟨KudosData⟩

  MethodId := Methods
  MethodArgs := fun
    | Methods.Transfer => ⟨TransferArgs⟩

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Mint => ⟨MintArgs⟩

  DestructorId := Destructors
  DestructorArgs := fun
    | Destructors.Burn => ⟨PUnit⟩

def label : Ecosystem.Label where
  name := "KudosEcosystem"
  ClassId := Classes
  classLabel := fun
    | Classes.Kudos => clab

def toObject (c : Kudos) : ObjectData clab where
  quantity := c.quantity
  privateFields := { originator := c.originator, owner := c.owner }

def fromObject (o : ObjectData clab) : Kudos :=
  { owner := o.privateFields.owner
    quantity := o.quantity
    originator := o.privateFields.originator }

instance hasIsObject : IsObject Kudos where
  label := label
  classId := Classes.Kudos
  toObject := Kudos.toObject
  fromObject := Kudos.fromObject

def kudosMint : @Class.Constructor label Classes.Kudos Constructors.Mint := defConstructor
  (body := fun (args : MintArgs) => ⟪
    return
      { quantity := args.quantity
        owner := args.originator
        originator := args.originator : Kudos}
  ⟫)
  (invariant := fun (args : MintArgs) => checkKey args.originator args.key)

def kudosTransfer : @Class.Method label Classes.Kudos Methods.Transfer := defMethod Kudos
  (body := fun (self : Kudos) (args : TransferArgs) =>
    ⟪return {self with owner := args.newOwner : Kudos}⟫)

def kudosBurn : @Class.Destructor label Classes.Kudos Destructors.Burn := defDestructor
  (invariant := fun (self : Kudos) (_args : PUnit) => self.originator == self.owner)

def kudosClass : @Class label Classes.Kudos where
  constructors := fun
    | Constructors.Mint => kudosMint
  methods := fun
    | Methods.Transfer => kudosTransfer
  destructors := fun
    | Destructors.Burn => kudosBurn
