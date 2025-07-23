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
  deriving BEq, Hashable, DecidableEq

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

namespace Account

def empty : Account where
  assets := ∅

instance instInhabited : Inhabited Account where
  default := empty

def isEmpty (a : Account) : Bool :=
  a.assets.values.all (fun n => n == 0)

set_option diagnostics true

instance instBEq : BEq Account where
  beq _a _b := false

def addTokens (a : Account) (d : Denomination) (n : Nat) : Account where
  assets := a.assets.modifyDefault d (fun v => v + n)

def subTokens (a : Account) (d : Denomination) (n : Nat) : Account where
  assets := a.assets.modify d (fun v => v - n)

def getBalance (a : Account) (d : Denomination) : Nat :=
  a.assets.get! d

end Account

structure Balances where
  accounts : Std.HashMap PublicKey Account

namespace Balances

-- TODO mock implementation
instance instBEq : BEq Balances where
  beq _a _b := true

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

deriving instance Inhabited for Balances

structure KudosBank where
  nfc : Anoma.NullifierKeyCommitment
  balances : Balances

namespace KudosBank

def new (nfc : Anoma.NullifierKeyCommitment) : KudosBank where
  nfc
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
  | New : Constructors
  deriving DecidableEq, Fintype, Repr

inductive Destructors where
  | Close : Destructors
  deriving DecidableEq, Fintype, Repr

deriving instance Inhabited for KudosBank

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

def clab : Class.Label where
  name := "KudosBank"
  PrivateFields := ⟨Balances⟩

  MethodId := Methods
  MethodArgs := fun
    | Methods.Transfer => ⟨TransferArgs⟩
    | Methods.Mint => ⟨MintArgs⟩
    | Methods.Burn => ⟨BurnArgs⟩

  ConstructorId := Constructors
  ConstructorArgs := fun
    | Constructors.New => ⟨Anoma.NullifierKeyCommitment⟩

  DestructorId := Destructors
  DestructorArgs := fun
    | Destructors.Close => ⟨UUnit⟩

namespace KudosBank

def toObject (c : KudosBank) : Object clab where
  quantity := 1
  privateFields := c.balances
  nullifierKeyCommitment := c.nfc

def fromObject (o : Object clab) : Option KudosBank := do
  let key <- o.nullifierKeyCommitment
  some { nfc := key
         balances := o.privateFields }

instance instIsObject : IsObject KudosBank where
  label := clab
  toObject := KudosBank.toObject
  fromObject := KudosBank.fromObject
  roundTrip : KudosBank.fromObject ∘ KudosBank.toObject = some := by rfl

end KudosBank

def kudosNew : @Class.Constructor clab Constructors.New := defConstructor
  (body := fun (nfc : Anoma.NullifierKeyCommitment) => KudosBank.new nfc)
  (invariant := fun (_args : Anoma.NullifierKeyCommitment) => true)

def kudosMint : @Class.Method clab Methods.Mint := defMethod KudosBank
  (body := fun (self : KudosBank) (args : MintArgs) =>
    [self.overBalances (fun b => b.addTokens args.denom.originator args.denom args.quantity)])
  (invariant := fun (_self : KudosBank) (args : MintArgs) => checkKey args.denom.originator args.key)

def kudosTransfer : @Class.Method clab Methods.Transfer := defMethod KudosBank
  (body := fun (self : KudosBank) (args : TransferArgs) =>
    [self.overBalances (fun b => b
      |> Balances.addTokens args.newOwner args.denom args.quantity
      |> Balances.subTokens args.oldOwner args.denom args.quantity)])
  (invariant := fun (self : KudosBank) (args : TransferArgs) =>
    checkKey args.oldOwner args.key
    && 0 < args.quantity
    && args.quantity <= self.getBalance args.oldOwner args.denom)

def kudosBurn : @Class.Method clab Methods.Burn := defMethod KudosBank
  (body := fun (self : KudosBank) (args : BurnArgs) =>
    [self.overBalances (fun b => b
      |> Balances.subTokens args.denom.originator args.denom args.quantity)])
  (invariant := fun (self : KudosBank) (args : BurnArgs) =>
    checkKey args.denom.originator args.key
    && 0 < args.quantity
    && args.quantity <= self.getBalance args.denom.originator args.denom)

def kudosClose : @Class.Destructor clab Destructors.Close := defDestructor
  (invariant := fun (self : KudosBank) (_args : UUnit) => self.balances.isEmpty)

inductive Functions where
  deriving Repr, DecidableEq, FinEnum

def lab : Ecosystem.Label where
  name := "KudosBank"
  ClassId := UUnit
  classLabel := fun _ => clab
  classId := fun _ => none -- FIXME
  FunctionId := Functions
  FunctionObjectArgClass {f : Functions} (_a : _) := nomatch f

def kudosClass : @Class lab UUnit.unit where
  constructors := fun
    | Constructors.New => kudosNew
  methods := fun
    | Methods.Transfer => kudosTransfer
    | Methods.Mint => kudosMint
    | Methods.Burn => kudosBurn
  intents := noIntents lab clab
  destructors := fun
    | Destructors.Close => kudosClose
  invariant _ _ := True

def kudosEcosystem : Ecosystem lab where
  classes := fun _ => kudosClass
  functions (f : Functions) := nomatch f
