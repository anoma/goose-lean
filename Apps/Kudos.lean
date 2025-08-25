import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib

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
/-           such that the aggregate quantity is equal to the original -/
/- 4. Burn: The owner of a kudos token can destroy it if themself is the originator of the token -/
/- 5. Merge: Merge two Kudos object of the same denomination and owner into a single one -/

structure KudosData where
  originator : PublicKey
  owner : PublicKey
  deriving DecidableEq, Inhabited

structure Kudos extends KudosData where
  quantity : Nat
  deriving DecidableEq, Inhabited

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

structure SplitArgs where
  quantities : List Nat
  deriving DecidableEq

instance SplitArgs.hasTypeRep : TypeRep SplitArgs where
  rep := Rep.atomic "SplitArgs"

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
    | Methods.Split => ⟨SplitArgs⟩
    | Methods.Transfer => ⟨TransferArgs⟩

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Mint => ⟨MintArgs⟩

  DestructorId := Destructors
  DestructorArgs := fun
    | Destructors.Burn => ⟨PUnit⟩

def toObject (c : Kudos) : Object clab where
  quantity := c.quantity
  privateFields := { originator := c.originator, owner := c.owner }

def fromObject (o : Object clab) : Option Kudos := do
  some { owner := o.privateFields.owner
         quantity := o.quantity
         originator := o.privateFields.originator }

instance hasIsObject : IsObject Kudos where
  label := clab
  toObject := Kudos.toObject
  fromObject := Kudos.fromObject
  roundTrip : Kudos.fromObject ∘ Kudos.toObject = some := by rfl

def kudosMint : @Class.Constructor clab Constructors.Mint := defConstructor
  (body := fun (args : MintArgs) => { quantity := args.quantity
                                      owner := args.originator
                                      originator := args.originator : Kudos})
  (invariant := fun (args : MintArgs) => checkKey args.originator args.key)

def kudosSplit : @Class.Method clab Methods.Split := defMethod Kudos
  (body := fun (self : Kudos) (args : SplitArgs) =>
    let mk (q : Nat) : Kudos := {self with quantity := q}
    List.map (IsObject.toAnObject ∘ mk) args.quantities)

def kudosTransfer : @Class.Method clab Methods.Transfer := defMethod Kudos
  (body := fun (self : Kudos) (args : TransferArgs) =>
    [{self with owner := args.newOwner : Kudos}])

def kudosBurn : @Class.Destructor clab Destructors.Burn := @defDestructor Kudos
  (invariant := fun (self : Kudos) (_args : PUnit) => self.originator == self.owner)

inductive Functions where
  | Merge
  deriving Repr, DecidableEq, FinEnum

export Functions (Merge)

namespace Merge

inductive ArgNames where
  | Kudos1
  | Kudos2
  deriving DecidableEq, Repr, FinEnum

export ArgNames (Kudos1 Kudos2)

end Merge

def lab : Ecosystem.Label where
  name := "Kudos"
  ClassId := PUnit
  classLabel := fun _ => clab
  FunctionId := Functions
  FunctionObjectArgClass {f : Functions} (_a : _) := match f with
   | Merge => PUnit.unit
  FunctionObjectArgNames : Functions → Type := fun
   | Merge => Merge.ArgNames

def kudosClass : @Class lab PUnit.unit  where
  constructors := fun
    | Constructors.Mint => kudosMint
  methods := fun
    | Methods.Split => kudosSplit
    | Methods.Transfer => kudosTransfer
  intents := noIntents lab clab
  destructors := fun
    | Destructors.Burn => kudosBurn

def kudosEcosystem : Ecosystem lab where
  classes := fun _ => kudosClass
  functions (f : Functions) := match f with
    | .Merge =>
      let mergeArgsInfo (a : lab.FunctionObjectArgNames Merge)
      : ObjectArgInfo lab Merge a :=
      match a with
      | .Kudos1 => { type := Kudos }
      | .Kudos2 => { type := Kudos }

      defFunction lab Merge
        (argsInfo := mergeArgsInfo)
        (body := fun kudos _args =>
                  let k1 := kudos .Kudos1
                  let k2 := kudos .Kudos2
                  {created := [{k1 with quantity := k1.quantity + k2.quantity : Kudos}]})
        (invariant := fun kudos _args =>
                  let k1 := kudos .Kudos1
                  let k2 := kudos .Kudos2
                  k1.originator == k2.originator
                  && k1.owner == k2.owner)
