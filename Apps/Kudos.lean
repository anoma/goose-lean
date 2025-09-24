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

namespace Methods

inductive Transfer.SignatureId : Type where
  | owner
 deriving DecidableEq, FinEnum

abbrev SignatureId : Methods → Type
 | .Transfer => Transfer.SignatureId

end Methods

inductive Constructors where
  | Mint : Constructors
  deriving DecidableEq, Fintype, Repr

namespace Constructors

inductive Mint.SignatureId where
  | originator
 deriving DecidableEq, FinEnum

abbrev SignatureId (m : Constructors) : Type :=
  match m with
  | .Mint => Mint.SignatureId

end Constructors

inductive Destructors where
  | Burn : Destructors
  deriving DecidableEq, Fintype, Repr

namespace Destructors

inductive Burn.SignatureId : Type where
  | owner
 deriving DecidableEq, FinEnum

abbrev SignatureId : Destructors → Type
 | .Burn => Burn.SignatureId

end Destructors

inductive Classes where
  | Kudos : Classes
  deriving DecidableEq, FinEnum, Repr

open AVM

instance KudosData.hasTypeRep : TypeRep KudosData where
  rep := Rep.atomic "KudosData"

instance hasTypeRep : TypeRep Kudos where
  rep := Rep.atomic "Kudos"

structure MintArgs where
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
  MethodSignatureId := Methods.SignatureId

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Mint => ⟨MintArgs⟩
  ConstructorSignatureId := Constructors.SignatureId

  DestructorId := Destructors
  DestructorArgs := fun
    | Destructors.Burn => ⟨PUnit⟩
  DestructorSignatureId := Destructors.SignatureId

def label : Ecosystem.Label := Ecosystem.Label.singleton clab

def toObject (c : Kudos) : @ObjectData label .unit where
  quantity := c.quantity
  privateFields := { originator := c.originator, owner := c.owner }

def fromObject (o : @ObjectData label .unit) : Kudos :=
  { owner := o.privateFields.owner
    quantity := o.quantity
    originator := o.privateFields.originator }

instance hasIsObject : IsObject Kudos where
  label := label
  classId := .unit
  isObjectOf :=
    { toObject := Kudos.toObject
      fromObject := Kudos.fromObject }

def kudosMint : @Class.Constructor label .unit Constructors.Mint := defConstructor
  (body := fun (args : MintArgs) => ⟪
    return
      { quantity := args.quantity
        owner := args.originator
        originator := args.originator : Kudos}
  ⟫)
  (invariant := fun (args : MintArgs) signatures => checkSignature (signatures .originator) args.originator)

def kudosTransfer : @Class.Method label .unit Methods.Transfer := defMethod Kudos
  (body := fun (self : Kudos) (args : TransferArgs) =>
    ⟪return {self with owner := args.newOwner : Kudos}⟫)
  (invariant := fun (self : Kudos) (_args : TransferArgs) signatures =>
    checkSignature (signatures .owner) self.owner)

def kudosBurn : @Class.Destructor label .unit Destructors.Burn := defDestructor
  (invariant := fun (self : Kudos) (_args : PUnit) signatures =>
    checkSignature (signatures .owner) self.owner
    && self.originator == self.owner)

def kudosClass : @Class label .unit where
  constructors := fun
    | Constructors.Mint => kudosMint
  methods := fun
    | Methods.Transfer => kudosTransfer
  destructors := fun
    | Destructors.Burn => kudosBurn
