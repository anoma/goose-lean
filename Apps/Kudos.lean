import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib

/-- Public name of someone -/
abbrev PublicIden := Anoma.NullifierKeyCommitment

/-- Kudos API Summary: -/
/- 1. For this example, we define public key = NullifierKeyCommitment and private key = NullifierKey -/
/- 2. Definition of *ownership*: We say that a user owns a resource R if it knows the -/
/-   NullifierKey that corresponds to the R.nullifierKeyCommitment  -/
/- 3. Definition of *kudos token*: A kudos token has three parameters: -/
/-    2.1. The quantity -/
/-    2.2. The originator: The public key of the user that minted this token -/
/-    2.3. The owner: The public key of the user that owns this token -/
/- The following operations are supported: -/
/- 1. Minting: Any user with public key K can mint any quantity of tokens with originator = owner = K -/
/- 2. Transfer: The onwer of a kudos token can transfer it to another user -/
/- 3. Split: The onwer of a kudos can partition a kudos token into a list of tokens with smaller quantities -/
/- 4. Burn: The owner of a kudos token can destroy it if themself is the originator of the token -/

structure Kudos where
  quantity : Nat
  originator : PublicIden
  owner : PublicIden
  deriving DecidableEq

namespace Kudos

inductive Methods where
  | Split : Methods
  | Transfer : Methods
  deriving DecidableEq, Fintype, Repr

inductive Constructors where
  | Mint : Constructors
  deriving DecidableEq, Fintype, Repr

inductive Destructors where
  | Burn : Destructors
  deriving DecidableEq, Fintype, Repr

deriving instance Inhabited for Kudos

open AVM

instance hasTypeRep : TypeRep Kudos where
  rep := Rep.atomic "Kudos"

structure MintArgs where
  key : Anoma.NullifierKey
  quantity : Nat
  deriving BEq

instance MintArgs.hasTypeRep : TypeRep MintArgs where
  rep := Rep.atomic "MintArgs"

structure SplitArgs where
  quantities : List Nat
  deriving DecidableEq

instance SplitArgs.hasTypeRep : TypeRep SplitArgs where
  rep := Rep.atomic "SplitArgs"

structure TransferArgs where
  newOwner : PublicIden
  deriving DecidableEq

instance TransferArgs.hasTypeRep : TypeRep TransferArgs where
  rep := Rep.atomic "TransferArgs"

def lab : Class.Label where
  name := "Kudos"
  PrivateFields := ⟨PublicIden⟩
  PublicFields := ⟨Unit⟩

  MethodId := Methods
  MethodArgs := fun
    | Methods.Split => ⟨SplitArgs⟩
    | Methods.Transfer => ⟨TransferArgs⟩

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Mint => ⟨MintArgs⟩

  DestructorId := Destructors
  DestructorArgs := fun
    | Destructors.Burn => ⟨UUnit⟩

def toObject (c : Kudos) : Object lab where
  publicFields := Unit.unit
  quantity := c.quantity
  privateFields := c.originator
  nullifierKeyCommitment := c.owner

def fromObject (o : Object lab) : Option Kudos := do
  let key <- o.nullifierKeyCommitment
  some { owner := key
         quantity := o.quantity
         originator := o.privateFields }

instance hasIsObject : IsObject Kudos where
  lab := lab
  toObject := Kudos.toObject
  fromObject := Kudos.fromObject
  roundTrip : Kudos.fromObject ∘ Kudos.toObject = some := by rfl

def kudosMint : @Class.Constructor lab Constructors.Mint := defConstructor Kudos
  (body := fun (args : MintArgs) => { quantity := args.quantity
                                      owner := args.key.commitment
                                      originator := args.key.commitment })
  (invariant := fun (_args : MintArgs) => true)

def kudosSplit : @Class.Method lab Methods.Split := defMethod Kudos
  (body := fun (self : Kudos) (args : SplitArgs) =>
    let mk (q : Nat) : Kudos := {self with quantity := q}
    List.map (IsObject.toAnObject ∘ mk) args.quantities)
  (invariant := fun (_self : Kudos) (_args : SplitArgs) => true)

def kudosTransfer : @Class.Method lab Methods.Transfer := defMethod Kudos
  (body := fun (self : Kudos) (args : TransferArgs) =>
    [{self with owner := args.newOwner : Kudos}])
  (invariant := fun (_self : Kudos) (_args : TransferArgs) => true)

def kudosBurn : @Class.Destructor lab Destructors.Burn := defDestructor Kudos
  (invariant := fun (self : Kudos) (_args : UUnit) => self.originator == self.owner)

def kudosClass : Class lab where
  constructors := fun
    | Constructors.Mint => kudosMint
  methods := fun
    | Methods.Split => kudosSplit
    | Methods.Transfer => kudosTransfer
  intents := fun x => nomatch x
  destructors := fun
    | Destructors.Burn => kudosBurn
  invariant _ _ := True
