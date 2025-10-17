import AVM
import Applib

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
  deriving DecidableEq, Inhabited, Hashable

structure Kudos extends KudosData where
  quantity : Nat
  deriving DecidableEq, Inhabited, Hashable

namespace Kudos

inductive Methods where
  | Transfer : Methods
  deriving DecidableEq, FinEnum, Repr

namespace Methods

inductive Transfer.SignatureId : Type where
  | owner
 deriving DecidableEq, FinEnum

abbrev SignatureId : Methods → Type
 | .Transfer => Transfer.SignatureId

end Methods

inductive Constructors where
  | Mint : Constructors
  deriving DecidableEq, FinEnum, Repr

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
  deriving DecidableEq, FinEnum, Repr

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
  deriving BEq, Hashable

instance MintArgs.hasTypeRep : TypeRep MintArgs where
  rep := Rep.atomic "MintArgs"

structure TransferArgs where
  newOwner : PublicKey
  deriving DecidableEq, Hashable

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

inductive MultiMethods where
  | Merge
  | Split
  deriving Repr, DecidableEq, FinEnum

export MultiMethods (Merge)

namespace Merge

inductive ArgNames where
  | Kudos1
  | Kudos2
  deriving DecidableEq, Repr, FinEnum

export ArgNames (Kudos1 Kudos2)

structure Args where
  deriving BEq, Hashable

instance Args.hasTypeRep : TypeRep Args where
  rep := Rep.atomic "Kudos.Merge.Args"

end Merge

namespace Split

inductive ArgNames where
  | Kudos
  deriving DecidableEq, Repr, FinEnum

export ArgNames (Kudos)

structure Args where
  quantities : List Nat
  deriving BEq, Hashable

instance Args.hasTypeRep : TypeRep Args where
  rep := Rep.atomic "Kudos.Split.Args"

end Split

def label : Ecosystem.Label where
  name := "Kudos"
  ClassId := PUnit
  classLabel := fun _ => clab
  MultiMethodId := MultiMethods
  MultiMethodArgs := fun
    | .Merge => ⟨Merge.Args⟩
    | .Split => ⟨Split.Args⟩
  MultiMethodObjectArgClass {f : MultiMethods} (_a : _) := match f with
    | .Merge => PUnit.unit
    | .Split => PUnit.unit
  MultiMethodObjectArgNames : MultiMethods → Type := fun
    | .Merge => Merge.ArgNames
    | .Split => Split.ArgNames
  ObjectArgNamesBEq (f : MultiMethods) := by cases f <;> exact inferInstance
  ObjectArgNamesEnum (f : MultiMethods) := by cases f <;> exact inferInstance

def toObject (c : Kudos) : @ObjectData label .unit where
  quantity := c.quantity
  privateFields := { originator := c.originator, owner := c.owner }

def fromObject (o : @ObjectData label .unit) : Kudos :=
  { owner := o.privateFields.owner
    quantity := o.quantity
    originator := o.privateFields.originator }

instance instIsObjectOf : @IsObjectOf label () Kudos where
  toObject := Kudos.toObject
  fromObject := Kudos.fromObject

instance instIsObject : IsObject Kudos where
  label := label
  classId := .unit
  isObjectOf := inferInstance

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

def kudosEcosystem : Ecosystem label where
  classes := fun _ => kudosClass
  multiMethods (f : MultiMethods) := match f with
    | .Merge =>
      let mergeArgsInfo (a : label.MultiMethodObjectArgNames Merge)
      : ObjectArgInfo label Merge a :=
      match a with
      | .Kudos1 => { type := Kudos, isObjectOf := Kudos.instIsObjectOf }
      | .Kudos2 => { type := Kudos, isObjectOf := Kudos.instIsObjectOf }

      defMultiMethod label Merge
        (argsInfo := mergeArgsInfo)
        (body := fun kudos _args => ⟪
                  let k1 := kudos .Kudos1
                  let k2 := kudos .Kudos2
                  return {
                    assembled := {
                      withOldUid _ _ := none
                      withNewUid :=
                        [{k1 with quantity := k1.quantity + k2.quantity : Kudos}]
                    }
                  }
                ⟫)
        (invariant := fun kudos _args _signatures =>
                  let k1 := kudos .Kudos1
                  let k2 := kudos .Kudos2
                  k1.originator == k2.originator
                  && k1.owner == k2.owner)

    | .Split =>
      let splitArgsInfo (a : label.MultiMethodObjectArgNames .Split)
      : ObjectArgInfo label .Split a :=
      match a with
      | .Kudos => { type := Kudos, isObjectOf := Kudos.instIsObjectOf }

      defMultiMethod label .Split
        (argsInfo := splitArgsInfo)
        (body := fun kudos args => ⟪
                  let k := kudos .Kudos
                  return {
                    assembled := {
                      withOldUid _ _ := none
                      withNewUid :=
                        let mk (q : Nat) : Kudos := {k with quantity := q}
                        List.map (IsObject.toAnObject ∘ mk) args.quantities
                    }
                  }
                ⟫)
