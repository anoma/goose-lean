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
  deriving BEq, Hashable, DecidableEq

structure Account where
  assets : Std.HashMap Denomination Nat
  deriving BEq

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
  deriving BEq

namespace Check

open AVM

instance hasTypeRep : TypeRep Check where
  rep := Rep.atomic "Check"

inductive Methods where
  | Transfer
  deriving Repr, BEq, Fintype

structure TransferArgs where
  newOwner : PublicKey
  key : PrivateKey
  deriving DecidableEq

instance TransferArgs.hasTypeRep : TypeRep TransferArgs where
  rep := Rep.atomic "Check.TransferArgs"

def Label : Class.Label where
  name := "Check"
  PrivateFields := ⟨Check⟩
  SubObjects := noSubObjects

  MethodId := Methods
  MethodArgs := fun _ => ⟨TransferArgs⟩

  ConstructorId := Empty
  ConstructorArgs := noConstructors

  DestructorId := Empty
  DestructorArgs := noDestructors

instance instIsObject : IsObject Check where
  label := Label
  toObject := fun (c : Check) =>
   { quantity := 1
     privateFields := c }
  fromObject := fun (o : Object Label) => some o.privateFields
  roundTrip := by rfl

end Check

structure Auction where
  owner : PublicKey
  auctionedDenomination : Denomination
  auctionedQuantity : Nat
  biddingDenomination : Denomination
  highestBid : Nat
  highestBidder : PublicKey
  deriving BEq

namespace Auction

open AVM

instance hasTypeRep : TypeRep Auction where
  rep := Rep.atomic "Auction"

def Label : Class.Label where
  name := "Auction"
  PrivateFields := ⟨Auction⟩
  SubObjects := noSubObjects

  MethodId := Empty
  MethodArgs := noMethods

  ConstructorId := Empty
  ConstructorArgs := noConstructors

  DestructorId := Empty
  DestructorArgs := noDestructors

instance instIsObject : IsObject Auction where
  label := Label
  toObject := fun (c : Auction) =>
   { quantity := 1
     privateFields := c }
  fromObject := fun (o : Object Label) => some o.privateFields
  roundTrip := by rfl

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

inductive Constructors where
  | Open : Constructors
  deriving DecidableEq, Fintype, Repr

inductive Destructors where
  | Close : Destructors
  deriving DecidableEq, Fintype, Repr

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
  quantity : Nat
  key : PrivateKey
  deriving DecidableEq

instance BurnArgs.hasTypeRep : TypeRep BurnArgs where
  rep := Rep.atomic "BurnArgs"

def BankLabel : Class.Label where
  name := "KudosBank"
  PrivateFields := ⟨KudosBank⟩
  SubObjects := noSubObjects

  MethodId := Methods
  MethodArgs := fun
    | Methods.Transfer => ⟨TransferArgs⟩
    | Methods.Mint => ⟨MintArgs⟩
    | Methods.Burn => ⟨BurnArgs⟩

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.Open => ⟨PublicKey⟩

  DestructorId := Destructors
  DestructorArgs := fun
    | Destructors.Close => ⟨UUnit⟩

namespace KudosBank

def toObject (c : KudosBank) : Object BankLabel where
  quantity := 1
  privateFields := c

def fromObject (o : Object BankLabel) : Option KudosBank :=
  some o.privateFields

instance instIsObject : IsObject KudosBank where
  label := BankLabel
  toObject := KudosBank.toObject
  fromObject := KudosBank.fromObject
  roundTrip : KudosBank.fromObject ∘ KudosBank.toObject = some := by rfl

end KudosBank

def kudosNew : @Class.Constructor BankLabel Constructors.Open := defConstructor
  (body := fun (owner : PublicKey) => KudosBank.new owner)

def kudosMint : @Class.Method BankLabel Methods.Mint := defMethod KudosBank
  (body := fun (self : KudosBank) (args : MintArgs) =>
    [self.overBalances (fun b => b.addTokens args.denom.originator args.denom args.quantity)])
  (invariant := fun (_self : KudosBank) (args : MintArgs) => checkKey args.denom.originator args.key)

def kudosTransfer : @Class.Method BankLabel Methods.Transfer := defMethod KudosBank
  (body := fun (self : KudosBank) (args : TransferArgs) =>
    [self.overBalances (fun b => b
      |> Balances.addTokens args.newOwner args.denom args.quantity
      |> Balances.subTokens args.oldOwner args.denom args.quantity)])
  (invariant := fun (self : KudosBank) (args : TransferArgs) =>
    checkKey args.oldOwner args.key
    && 0 < args.quantity
    && args.quantity <= self.getBalance args.oldOwner args.denom)

def kudosBurn : @Class.Method BankLabel Methods.Burn := defMethod KudosBank
  (body := fun (self : KudosBank) (args : BurnArgs) =>
    [self.overBalances (fun b => b
      |> Balances.subTokens args.denom.originator args.denom args.quantity)])
  (invariant := fun (self : KudosBank) (args : BurnArgs) =>
    checkKey args.denom.originator args.key
    && 0 < args.quantity
    && args.quantity <= self.getBalance args.denom.originator args.denom)

def kudosClose : @Class.Destructor BankLabel Destructors.Close := defDestructor
  (invariant := fun (self : KudosBank) (_args : UUnit) => self.balances.isEmpty)

inductive Functions where
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

def lab : Ecosystem.Label where
  name := "KudosBank"
  ClassId := Classes
  classLabel := fun
   | .Bank => BankLabel
   | .Check => Check.Label
   | .Auction => Auction.Label
  FunctionId := Functions
  FunctionArgs := fun
    | .IssueCheck => ⟨IssueCheck.Args⟩
    | .DepositCheck => ⟨DepositCheck.Args⟩
    | .NewAuction => ⟨NewAuction.Args⟩
    | .Bid => ⟨Bid.Args⟩
    | .EndAuction => ⟨EndAuction.Args⟩
  FunctionObjectArgNames := fun
    | .IssueCheck => IssueCheck.ClassArgNames
    | .DepositCheck => DepositCheck.ClassArgNames
    | .NewAuction => NewAuction.ClassArgNames
    | .Bid => Bid.ClassArgNames
    | .EndAuction => EndAuction.ClassArgNames
  FunctionObjectArgClass {f : Functions} := match f with
   | Functions.IssueCheck => fun
     | .bank => Classes.Bank
   | Functions.DepositCheck => fun
     | .bank => Classes.Bank
     | .check => Classes.Check
   | Functions.NewAuction => fun
     | .check => Classes.Check
   | Functions.Bid => fun
     | .check => Classes.Check
     | .auction => Classes.Auction
   | Functions.EndAuction => fun
     | .auction => Classes.Auction
  objectArgNamesBEq (f : Functions) := by cases f <;> exact inferInstance
  objectArgNamesEnum (f : Functions) := by cases f <;> exact inferInstance

def kudosClass : @Class lab Classes.Bank where
  constructors := fun
    | Constructors.Open => kudosNew
  methods := fun
    | .Transfer => kudosTransfer
    | .Mint => kudosMint
    | .Burn => kudosBurn
  intents := noIntents lab BankLabel
  destructors := fun
    | .Close => kudosClose

def checkTransfer : @Class.Method Check.Label .Transfer := defMethod Check
  (body := fun (self : Check) (args : Check.TransferArgs) =>
    [{self with owner := args.newOwner : Check}])
  (invariant := fun (self : Check) (args : Check.TransferArgs) =>
    checkKey self.owner args.key)

def checkClass : @Class lab Classes.Check where
  constructors := noConstructors
  methods := fun
    | .Transfer => checkTransfer
  intents := noIntents lab Check.Label
  destructors := noDestructors

def issueCheck : @Function lab .IssueCheck :=
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

def auctionClass : @Class lab Classes.Auction where
  constructors := noConstructors
  methods := noMethods
  intents := noIntents lab Auction.Label
  destructors := noDestructors

def kudosEcosystem : Ecosystem lab where
  classes := fun
    | .Bank => kudosClass
    | .Check => checkClass
    | .Auction => auctionClass
  functions := fun
    | .IssueCheck => issueCheck
    | .DepositCheck => depositCheck
    | .NewAuction => newAuction
    | .Bid => bid
    | .EndAuction => endAuction
