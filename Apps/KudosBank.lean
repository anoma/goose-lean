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
 deriving DecidableEq, FinEnum

inductive Mint.SignatureId where
  | owner
 deriving DecidableEq, FinEnum

inductive Burn.SignatureId where
  | owner
  | originator
 deriving DecidableEq, FinEnum

abbrev SignatureId (m : Methods) : Type :=
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
 deriving DecidableEq, FinEnum

abbrev SignatureId : Destructors → Type
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

inductive MultiMethods where
  | IssueCheck
  | DepositCheck
  | NewAuction
  | Bid
  | EndAuction
  deriving Repr, DecidableEq, FinEnum

namespace IssueCheck

structure Args where
  denomination : Denomination
  owner : PublicKey
  key : PrivateKey
  quantity : Nat
  deriving BEq

inductive ClassArgNames where
  | bank
  deriving Repr, BEq, DecidableEq, FinEnum

instance Args.hasTypeRep : TypeRep Args where
  rep := Rep.atomic "IssueCheck.Args"

end IssueCheck

namespace DepositCheck

structure Args where
  key : PrivateKey
  deriving BEq

instance Args.hasTypeRep : TypeRep Args where
  rep := Rep.atomic "DepositCheck.Args"

inductive ClassArgNames where
  | bank
  | check
  deriving Repr, BEq, DecidableEq, FinEnum

end DepositCheck

namespace NewAuction

structure Args where
  biddingDenomination : Denomination
  key : PrivateKey
  deriving BEq

instance Args.hasTypeRep : TypeRep Args where
  rep := Rep.atomic "NewAuction.Args"

inductive ClassArgNames where
  | check
  deriving Repr, BEq, DecidableEq, FinEnum

end NewAuction

namespace Bid

structure Args where
  key : PrivateKey
  deriving BEq

instance Args.hasTypeRep : TypeRep Args where
  rep := Rep.atomic "Bid.Args"

inductive ClassArgNames where
  | check
  | auction
  deriving Repr, BEq, DecidableEq, FinEnum

end Bid

namespace EndAuction

structure Args where
  key : PrivateKey
  deriving BEq

instance Args.hasTypeRep : TypeRep Args where
  rep := Rep.atomic "EndAuction.Args"

inductive ClassArgNames where
  | auction
  deriving Repr, BEq, DecidableEq, FinEnum

end EndAuction

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

  MultiMethodId := MultiMethods
  MultiMethodArgs := fun
    | .IssueCheck => ⟨IssueCheck.Args⟩
    | .DepositCheck => ⟨DepositCheck.Args⟩
    | .NewAuction => ⟨NewAuction.Args⟩
    | .Bid => ⟨Bid.Args⟩
    | .EndAuction => ⟨EndAuction.Args⟩
  MultiMethodObjectArgNames := fun
    | .IssueCheck => IssueCheck.ClassArgNames
    | .DepositCheck => DepositCheck.ClassArgNames
    | .NewAuction => NewAuction.ClassArgNames
    | .Bid => Bid.ClassArgNames
    | .EndAuction => EndAuction.ClassArgNames
  MultiMethodObjectArgClass {f : MultiMethods} := match f with
   | MultiMethods.IssueCheck => fun
     | .bank => Classes.Bank
   | MultiMethods.DepositCheck => fun
     | .bank => Classes.Bank
     | .check => Classes.Check
   | MultiMethods.NewAuction => fun
     | .check => Classes.Check
   | MultiMethods.Bid => fun
     | .check => Classes.Check
     | .auction => Classes.Auction
   | MultiMethods.EndAuction => fun
     | .auction => Classes.Auction
  ObjectArgNamesBEq (f : MultiMethods) := by cases f <;> exact inferInstance
  ObjectArgNamesEnum (f : MultiMethods) := by cases f <;> exact inferInstance

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
/-
def issueCheck : @Ecosystem.MultiMethod label .IssueCheck :=
  defFunction lab Functions.IssueCheck
  (argsInfo := fun
    | .bank => { type := KudosBank })
  (body := fun selves args =>
    { created :=
      [(selves .bank).overBalances (fun b => b
        |> Balances.subTokens args.owner args.denomination args.quantity)]

      constructed := [{ denomination := args.denomination
                        owner := args.owner
                        quantity := args.quantity
                        : Check }]})
  (invariant := fun selves args =>
    checkKey args.owner args.key
    && 0 < args.quantity
    && args.quantity <= (selves IssueCheck.ClassArgNames.bank
                         |>.getBalance args.owner args.denomination))

def depositCheck : @Function lab .DepositCheck :=
  defFunction lab .DepositCheck
  (argsInfo := fun
    | .bank => { type := KudosBank }
    | .check => { type := Check })
  (body := fun selves args =>
    { created :=
        let bank := selves .bank
        let check := selves .check
        [bank.overBalances (fun b => b
          |> Balances.addTokens check.owner check.denomination check.quantity)]
      argDeconstruction arg :=
        match arg with
        | .bank => .Disassembled
        | .check => .Destroyed })
  (invariant := fun selves args =>
    checkKey (selves .check).owner args.key)

def newAuction : @Function lab .NewAuction :=
  defFunction lab .NewAuction
  (argsInfo := fun
    | .check => { type := Check })
  (body := fun selves args =>
    { created :=
        let check := selves .check
        [ { owner := check.owner
            auctionedDenomination := check.denomination
            auctionedQuantity := check.quantity
            biddingDenomination := args.biddingDenomination
            highestBidder := check.owner
            highestBid := 0 : Auction} ]
      argDeconstruction arg :=
        match arg with
        | .check => .Destroyed })
  (invariant := fun selves args =>
    checkKey (selves .check).owner args.key)

def bid : @Function lab .Bid :=
  defFunction lab .Bid
  (argsInfo := fun
    | .check => { type := Check }
    | .auction => { type := Auction })
  (body := fun selves args =>
    let check := selves .check
    let auction := selves .auction
    { created :=
        [{ auction with
          highestBid := check.quantity
          highestBidder := check.owner
         : Auction }]
      constructed :=
        [{ denomination := auction.biddingDenomination
           owner := auction.highestBidder
           quantity := auction.highestBid : Check }]
      argDeconstruction arg :=
        match arg with
        | .check => .Destroyed
        | .auction => .Disassembled })
  (invariant := fun selves args =>
    let bid := selves .check
    let auction := selves .auction
    checkKey bid.owner args.key
    && bid.denomination == auction.biddingDenomination
    && bid.quantity > auction.highestBid)

def endAuction : @Function lab .EndAuction :=
  defFunction lab .EndAuction
  (argsInfo := fun
    | .auction => { type := Auction })
  (body := fun selves args =>
    let auction := selves .auction
    { created := []
      constructed :=
        let winnerCheck : Check :=
          { owner := auction.highestBidder
            denomination := auction.auctionedDenomination
            quantity := auction.auctionedQuantity }
        let ownerCheck : Check :=
          { owner := auction.owner
            quantity := auction.highestBid
            denomination := auction.biddingDenomination }
        [winnerCheck, ownerCheck]
      argDeconstruction arg :=
        match arg with
        | .auction => .Destroyed })
  (invariant := fun selves args =>
    let auction := selves .auction
    checkKey auction.owner args.key)

def kudosEcosystem : Ecosystem label where
  classes := fun
    | .Bank => kudosClass
    | .Check => checkClass
    | .Auction => auctionClass
  multiMethods := fun
    | .IssueCheck => issueCheck
    | .DepositCheck => depositCheck
    | .NewAuction => newAuction
    | .Bid => bid
    | .EndAuction => endAuction
-/
