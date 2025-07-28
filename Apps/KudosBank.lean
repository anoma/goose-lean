import AVM
import Applib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Applib

def Std.HashMap.modifyDefault
{α : Type u} {β : Type v} [BEq α] [Hashable α] [Inhabited β] (m : HashMap α β) (a : α) (f : β → β) : HashMap α β := m.alter a fun
  | none => some (f default)
  | some v => some (f v)

structure PublicKey where
  key : Nat
  deriving BEq, Hashable, DecidableEq, Inhabited

instance PublicKey.hasTypeRep : TypeRep PublicKey where
  rep := Rep.atomic "PublicKey"

structure PrivateKey where
  key : Nat
  deriving BEq, Hashable, DecidableEq

-- mock function
def checkKey (pub : PublicKey) (priv : PrivateKey) : Bool := pub.key == priv.key

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
  deriving Repr, DecidableEq, FinEnum

namespace IssueCheck

structure Args where
  denomination : Denomination
  owner : PublicKey
  key : PrivateKey
  quantity : Nat
  deriving BEq

inductive ClassArgNames where
  | Bank
  deriving Repr, BEq, DecidableEq, FinEnum

instance Args.hasTypeRep : TypeRep Args where
  rep := Rep.atomic "IssueCheck.Args"

end IssueCheck

namespace DepositCheck

inductive ClassArgNames where
  | Bank
  | Check
  deriving Repr, BEq, DecidableEq, FinEnum

end DepositCheck

inductive Classes where
  | Bank
  | Check
  deriving Repr, DecidableEq, FinEnum

def lab : Ecosystem.Label where
  name := "KudosBank"
  ClassId := Classes
  classLabel := fun
   | .Bank => BankLabel
   | .Check => Check.Label
  FunctionId := Functions
  FunctionArgs := fun
    | .IssueCheck => ⟨IssueCheck.Args⟩
    | .DepositCheck => ⟨UUnit⟩
  FunctionObjectArgNames := fun
    | .IssueCheck => IssueCheck.ClassArgNames
    | .DepositCheck => DepositCheck.ClassArgNames
  FunctionObjectArgClass {f : Functions} := match f with
   | Functions.IssueCheck => fun
     | _ => Classes.Bank
   | Functions.DepositCheck => fun
     | .Bank => Classes.Bank
     | .Check => Classes.Check
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
    | .Bank => { type := KudosBank })
  (body := fun selves args =>
    { created :=
      [(selves .Bank).overBalances (fun b => b
        |> Balances.subTokens args.owner args.denomination args.quantity)]

      constructed := [{ denomination := args.denomination
                        owner := args.owner
                        quantity := args.quantity
                        : Check }]})
  (invariant := fun selves args =>
    checkKey args.owner args.key
    && 0 < args.quantity
    && args.quantity <= (selves IssueCheck.ClassArgNames.Bank
                         |>.getBalance args.owner args.denomination))

def depositCheck : @Function lab .DepositCheck :=
  defFunction lab .DepositCheck
  (argsInfo := fun
    | .Bank => { type := KudosBank }
    | .Check => { type := Check })
  (body := fun selves args =>
    { created :=
        let bank := selves .Bank
        let check := selves .Check
        [bank.overBalances (fun b => b
          |> Balances.addTokens check.owner check.denomination check.quantity)]
      argDeconstruction arg :=
        match arg with
        | .Bank => .Disassembled
        | .Check => .Destroyed })


def kudosEcosystem : Ecosystem lab where
  classes := fun
    | Classes.Bank => kudosClass
    | Classes.Check => checkClass
  functions := fun
    | Functions.IssueCheck => issueCheck
    | Functions.DepositCheck => depositCheck
