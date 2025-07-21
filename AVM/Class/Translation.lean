import Mathlib.Control.Random
import Prelude
import Anoma
import AVM.Class
import AVM.Action
import AVM.Class.Label
import AVM.Ecosystem
import AVM.Object
import AVM.Object.Consumable
import AVM.Class.Member
import AVM.Logic

namespace AVM.Class

open Ecosystem
open AVM.Action

/-- Creates a logic for a given constructor. This logic is combined with other
    method and constructor logics to create the complete resource logic for an
    object. -/
def Constructor.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor constrId)
  (args : Logic.Args lab)
  : Bool :=
    if args.isConsumed then
      match SomeType.cast args.data.memberArgs with
      | some argsData =>
        let newObj := constr.created argsData
        Logic.checkResourceData [newObj.toSomeObject] args.consumed
          && Logic.checkResourceData [newObj.toSomeObject] args.created
          && constr.invariant argsData
      | none =>
        false
    else
      -- TODO: not general enough, fine for the counter
      true

def Constructor.action
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor constrId)
  (args : constrId.Args.type)
  : Rand (Anoma.Action × Anoma.DeltaWitness) :=
    -- TODO: set nonce properly
    let clab := classId.label
    let newObj : Object clab := constr.created args
    let consumable : ConsumableObject clab :=
       { object := {newObj with nullifierKeyCommitment := Anoma.NullifierKeyCommitment.universal}
         ephemeral := true
         key := Anoma.NullifierKey.universal }
    let consumed : ConsumedObject classId.label := { consumable with can_nullify := Anoma.nullifyUniversal consumable.resource consumable.key rfl rfl }
    let created : List CreatedObject :=
          [CreatedObject.fromSomeObject newObj.toSomeObject (ephemeral := false)
           (nonce := consumed.can_nullify.nullifier.toNonce)]
    Action.create lab (.classMember (.constructorId constrId)) args [consumed] created

/-- Creates an Anoma Transaction for a given object construtor. -/
def Constructor.transaction
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor constrId) (args : constrId.Args.type)
  : Rand Anoma.Transaction := do
    let (action, witness) ← constr.action args
    pure <|
      { actions := [action],
        -- TODO: automatically generate deltaProof that verifies that the transaction is balanced
        deltaProof := Anoma.Transaction.generateDeltaProof witness [action] }

/-- Creates a logic for a given method. This logic is combined with other method
    and constructor logics to create the complete resource logic for an object. -/
def Method.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {methodId : classId.label.MethodId}
  (method : Class.Method methodId)
  (args : Logic.Args lab)
  : Bool :=
    if args.isConsumed then
      match SomeType.cast args.data.memberArgs with
      | some argsData =>
        let mselfObj : Option (Object classId.label) := Object.fromResource args.self
        match mselfObj with
          | none => false
          | some selfObj =>
            method.invariant selfObj argsData
            && Logic.checkResourceData [selfObj.toSomeObject] args.consumed
            && let createdObjects := method.created selfObj argsData
               Logic.checkResourceData createdObjects args.created
      | none =>
        false
    else
      -- TODO: may need to do something more here in general, fine for the counter
      true

def Method.action
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (methodId : classId.label.MethodId)
  (method : Class.Method methodId)
  (self : Object classId.label)
  (key : Anoma.NullifierKey)
  (args : methodId.Args.type)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
  -- TODO: set nonce and nullifierKeyCommitment properly
  let consumable : ConsumableObject classId.label :=
      { key
        object := self
        ephemeral := false }
  match consumable.consume with
  | none => pure none
  | some consumed =>
    let createObject (o : SomeObject) : CreatedObject :=
      -- FIXME see https://github.com/anoma/goose-lean/issues/51
      let res : Anoma.Resource := o.toResource (ephemeral := false) (nonce := consumed.can_nullify.nullifier.toNonce)
      { object := o.object
        resource := res
        commitment := res.commitment }
    let created : List CreatedObject :=
        List.map createObject (method.created self args)
    Action.create lab (.classMember (.methodId methodId)) args [consumed] created

/-- Creates an Anoma Transaction for a given object method. -/
def Method.transaction
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (methodId : classId.label.MethodId)
  (method : Class.Method methodId)
  (self : Object classId.label)
  (key : Anoma.NullifierKey)
  (args : methodId.Args.type)
  : Rand (Option Anoma.Transaction) := do
  match ← method.action methodId self key args with
  | none => pure none
  | some (action, witness) =>
    pure <|
      some
        { actions := [action],
          deltaProof := Anoma.Transaction.generateDeltaProof witness [action] }

/-- Creates a logic for a given destructor. This logic is combined with other
    member logics to create the complete resource logic for an object. -/
def Destructor.logic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {destructorId : classId.label.DestructorId}
  (destructor : Class.Destructor destructorId)
  (args : Logic.Args lab)
  : Bool :=
    if args.isConsumed then
      match SomeType.cast args.data.memberArgs with
      | some argsData =>
        let mselfObj : Option (Object classId.label) := Object.fromResource args.self
        match mselfObj with
          | none => false
          | some selfObj =>
            Logic.checkResourceData [selfObj.toSomeObject] args.consumed
              && destructor.invariant selfObj argsData
      | none =>
        false
    else args.self.ephemeral

def Destructor.action
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (destructorId : classId.label.DestructorId)
  (_destructor : Class.Destructor destructorId)
  (self : Object classId.label)
  (key : Anoma.NullifierKey)
  (args : destructorId.Args.type)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
  let consumable : ConsumableObject classId.label :=
       { key
         object := self
         ephemeral := false }
  match consumable.consume with
  | none => pure none
  | some consumed =>
    let createdObject : CreatedObject :=
      let ephResource := { consumed.resource with ephemeral := true }
      { object := self
        resource := ephResource
        commitment := ephResource.commitment }
    Action.create lab (.classMember (.destructorId destructorId)) args [consumed] [createdObject]

/-- Creates an Anoma Transaction for a given object destructor. -/
def Destructor.transaction
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (destructorId : classId.label.DestructorId)
  (destructor : Class.Destructor destructorId)
  (self : Object classId.label)
  (key : Anoma.NullifierKey)
  (args : destructorId.Args.type)
  : Rand (Option Anoma.Transaction) := do
  match ← destructor.action destructorId self key args with
  | none => pure none
  | some (action, witness) =>
    pure <|
      some
        { actions := [action],
          deltaProof := Anoma.Transaction.generateDeltaProof witness [action] }

-- Check:
-- 1. member logic corresponding to the memberId in AppData
-- 2. class invariant for the object being consumed
def checkClassMemberLogic
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (args : Logic.Args lab)
  (eco : Ecosystem lab)
  (memberId : classId.label.MemberId)
  (margs : memberId.Args.type)
  : Bool := BoolCheck.run do
  let selfObj : Object classId.label ← BoolCheck.some (Object.fromResource args.self)
  let cls : Class classId := eco.classes classId
  BoolCheck.ret <|
    cls.invariant selfObj args &&
    match memberId with
    | .constructorId c =>
      Constructor.logic (cls.constructors c) args
    | .methodId m =>
      Method.logic (cls.methods m) args
    | .destructorId m =>
      Destructor.logic (cls.destructors m) args
