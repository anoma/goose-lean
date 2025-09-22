import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib

def Std.HashMap.modifyDefault
{α : Type u} {β : Type v} [BEq α] [Hashable α] [Inhabited β] (m : HashMap α β) (a : α) (f : β → β) : HashMap α β := m.alter a fun
  | none => some (f default)
  | some v => some (f v)

structure Denomination where
  originator : PublicKey
  deriving BEq, Inhabited, Hashable, DecidableEq

structure Account where
  assets : Std.HashMap Denomination Nat
  deriving BEq, Inhabited

namespace Account

def empty : Account where
  assets := ∅

instance instInhabited : Inhabited Account where
  default := empty

def isEmpty (a : Account) : Bool :=
  a.assets.values.all (fun n => n == 0)

def addTokens (a : Account) (d : Denomination) (n : Nat) : Account where
  assets := a.assets.modifyDefault d (fun v => v + n)

def subTokens (a : Account) (d : Denomination) (n : Nat) : Account where
  assets := a.assets.modify d (fun v => v - n)

def getBalance (a : Account) (d : Denomination) : Nat :=
  a.assets.get! d

end Account

structure Balances where
  accounts : Std.HashMap PublicKey Account
  deriving BEq, Inhabited

namespace Balances

def isEmpty (b : Balances) : Bool := b.accounts.values.all Account.isEmpty

def empty : Balances where
  accounts := ∅

def addTokens (p : PublicKey) (d : Denomination) (n : Nat) (b : Balances) : Balances where
  accounts := b.accounts.modifyDefault p (fun a => a.addTokens d n)

def subTokens (p : PublicKey) (d : Denomination) (n : Nat) (b : Balances) : Balances where
  accounts := b.accounts.modify p (fun a => a.subTokens d n)

def getBalance (b : Balances) (u : PublicKey) (d : Denomination) : Nat :=
  (b.accounts.get! u).getBalance d

end Balances

/-- Spending a check allows a user to make a transfer of a certain denomination -/
structure Check where
  denomination : Denomination
  owner : PublicKey
  quantity : Nat
  deriving BEq, Inhabited

namespace Check

open AVM

instance hasTypeRep : TypeRep Check where
  rep := Rep.atomic "Check"

inductive Methods where
  | Transfer
  deriving Repr, BEq, Fintype, DecidableEq

structure TransferArgs where
  newOwner : PublicKey
  key : PrivateKey
  deriving DecidableEq

instance TransferArgs.hasTypeRep : TypeRep TransferArgs where
  rep := Rep.atomic "Check.TransferArgs"

def Label : Class.Label where
  name := "Check"
  PrivateFields := ⟨Check⟩

  MethodId := Methods
  MethodArgs := fun _ => ⟨TransferArgs⟩

  ConstructorId := Empty
  ConstructorArgs := noConstructors

  DestructorId := Empty
  DestructorArgs := noDestructors

end Check

structure Auction where
  owner : PublicKey
  auctionedDenomination : Denomination
  auctionedQuantity : Nat
  biddingDenomination : Denomination
  highestBid : Nat
  highestBidder : PublicKey
  deriving BEq, Inhabited

namespace Auction

open AVM

instance hasTypeRep : TypeRep Auction where
  rep := Rep.atomic "Auction"

def Label : Class.Label where
  name := "Auction"
  PrivateFields := ⟨Auction⟩

  MethodId := Empty
  MethodArgs := noMethods

  ConstructorId := Empty
  ConstructorArgs := noConstructors

  DestructorId := Empty
  DestructorArgs := noDestructors

end Auction

structure KudosBank where
  owner : PublicKey
  balances : Balances
  deriving Inhabited, BEq

namespace KudosBank

def new (owner : PublicKey) : KudosBank where
  owner
  balances := Balances.empty

def overBalances (b : KudosBank) (f : Balances -> Balances) : KudosBank :=
  {b with balances := f b.balances}

def getBalance (b : KudosBank) (u : PublicKey) (d : Denomination) : Nat :=
  b.balances.getBalance u d

end KudosBank

inductive Methods where
  | Transfer : Methods
  | Mint : Methods
  | Burn : Methods
  deriving DecidableEq, Fintype, Repr

namespace Methods

inductive Transfer.SignatureId where
  | owner

inductive Mint.SignatureId where
  | owner

inductive Burn.SignatureId where
  | owner
  | originator

def SignatureId (m : Methods) : Type :=
  match m with
  | .Transfer => Transfer.SignatureId
  | .Mint => Mint.SignatureId
  | .Burn => Burn.SignatureId

end Methods

inductive Constructors where
  | Open : Constructors
  deriving DecidableEq, Fintype, Repr

inductive Destructors where
  | Close : Destructors
  deriving DecidableEq, Fintype, Repr

namespace Destructors

inductive Close.SignatureId : Type where
  | owner

def SignatureId : Destructors → Type
 | .Close => Close.SignatureId

end Destructors

open AVM

instance Balances.hasTypeRep : TypeRep Balances where
  rep := Rep.atomic "Balances"

instance hasTypeRep : TypeRep KudosBank where
  rep := Rep.atomic "KudosBank"

structure MintArgs where
  denom : Denomination
  key : PrivateKey
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
  oldOwner : PublicKey
  newOwner : PublicKey
  denom : Denomination
  quantity : Nat
  key : PrivateKey
  deriving DecidableEq

instance TransferArgs.hasTypeRep : TypeRep TransferArgs where
  rep := Rep.atomic "TransferArgs"

structure BurnArgs where
  denom : Denomination
  owner : PublicKey
  quantity : Nat
  deriving DecidableEq

instance BurnArgs.hasTypeRep : TypeRep BurnArgs where
  rep := Rep.atomic "BurnArgs"

def BankLabel : Class.Label where
  name := "KudosBank"
  PrivateFields := ⟨KudosBank⟩

  MethodId := Methods
  MethodArgs := fun
    | Methods.Transfer => ⟨TransferArgs⟩
    | Methods.Mint => ⟨MintArgs⟩
    | Methods.Burn => ⟨BurnArgs⟩
  MethodSignatureId := Methods.SignatureId

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Open => ⟨PublicKey⟩

  DestructorId := Destructors
  DestructorArgs := fun
    | Destructors.Close => ⟨PUnit⟩
  DestructorSignatureId := Destructors.SignatureId

inductive Classes where
  | Bank
  | Check
  | Auction
  deriving Repr, DecidableEq, FinEnum

def label : AVM.Ecosystem.Label where
  name := "KudosEcosystem"
  ClassId := Classes
  classLabel := fun
    | Classes.Bank => BankLabel
    | Classes.Check => Check.Label
    | Classes.Auction => Auction.Label
  MultiMethodObjectArgClass {f : Empty} := f.elim

instance Auction.instIsObject : IsObject Auction where
  label := label
  classId := Classes.Auction
  isObjectOf :=
    { toObject := fun (c : Auction) =>
       { quantity := 1
         privateFields := c }
      fromObject := fun (o : @ObjectData label Classes.Auction) => o.privateFields }

instance Check.instIsObject : IsObject Check where
  label := label
  classId := Classes.Check
  isObjectOf :=
    { toObject := fun (c : Check) =>
       { quantity := 1
         privateFields := c }
      fromObject := fun (o : @ObjectData label Classes.Check) => o.privateFields }

namespace KudosBank

def toObject (c : KudosBank) : @ObjectData label .Bank where
  quantity := 1
  privateFields := c

def fromObject (o : @ObjectData label .Bank) : KudosBank :=
  o.privateFields

instance instIsObject : IsObject KudosBank where
  label := label
  classId := Classes.Bank
  isObjectOf :=
    { toObject := KudosBank.toObject
      fromObject := KudosBank.fromObject }

end KudosBank

def kudosNew : @Class.Constructor label Classes.Bank Constructors.Open := defConstructor
  (body := fun (owner : PublicKey) => ⟪return KudosBank.new owner⟫)

def kudosMint : @Class.Method label Classes.Bank Methods.Mint := defMethod KudosBank
  (body := fun (self : KudosBank) (args : MintArgs) => ⟪
    return
      self.overBalances (fun b => b.addTokens args.denom.originator args.denom args.quantity)
  ⟫)

def kudosTransfer : @Class.Method label Classes.Bank Methods.Transfer := defMethod KudosBank
  (body := fun (self : KudosBank) (args : TransferArgs) => ⟪
    return
      self.overBalances (fun b => b
        |> Balances.addTokens args.newOwner args.denom args.quantity
        |> Balances.subTokens args.oldOwner args.denom args.quantity)
  ⟫)
  (invariant := fun (self : KudosBank) (args : TransferArgs) signatures =>
    0 < args.quantity
    && checkSignature (signatures .owner) args.oldOwner
    && args.quantity <= self.getBalance args.oldOwner args.denom)

def kudosBurn : @Class.Method label Classes.Bank Methods.Burn := defMethod KudosBank
  (body := fun (self : KudosBank) (args : BurnArgs) => ⟪
    return
      self.overBalances (fun b => b
        |> Balances.subTokens args.denom.originator args.denom args.quantity)
  ⟫)
  (invariant := fun (self : KudosBank) (args : BurnArgs) signatures =>
    checkSignature (signatures .originator) args.denom.originator
    && checkSignature (signatures .owner) args.owner
    && 0 < args.quantity
    && args.quantity <= self.getBalance args.denom.originator args.denom)

def kudosClose : @Class.Destructor label Classes.Bank Destructors.Close := defDestructor
  (invariant := fun (self : KudosBank) (_args : PUnit) signatures =>
    checkSignature (signatures .owner) self.owner
    && self.balances.isEmpty)

def kudosClass : @Class label Classes.Bank where
  constructors := fun
    | Constructors.Open => kudosNew
  methods := fun
    | .Transfer => kudosTransfer
    | .Mint => kudosMint
    | .Burn => kudosBurn
  destructors := fun
    | .Close => kudosClose

def checkTransfer : @Class.Method label Classes.Check .Transfer := defMethod Check
  (body := fun (self : Check) (args : Check.TransferArgs) => ⟪
    return
      {self with owner := args.newOwner : Check}
  ⟫)

def checkClass : @Class label Classes.Check where
  constructors := noConstructors
  methods := fun
    | .Transfer => checkTransfer
  destructors := noDestructors

def auctionClass : @Class label Classes.Auction where
  constructors := noConstructors
  methods := noMethods
  destructors := noDestructors
