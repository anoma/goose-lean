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
  let try argsData := SomeType.cast args.data.memberArgs
  let newObj := constr.created argsData
  Logic.checkResourcesData [newObj.toSomeObject] args.consumed
    && Logic.checkResourcesData [newObj.toSomeObject] args.created
    && Logic.checkResourcesEphemeral args.consumed
    && Logic.checkResourcesPersistent args.created
    && constr.invariant argsData

/-- Creates an action for a given constructor. This action consumes creates the
  object specified by the constructor. -/
def Constructor.action
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {constrId : classId.label.ConstructorId}
  (constr : Class.Constructor constrId)
  (args : constrId.Args.type)
  : Rand (Anoma.Action × Anoma.DeltaWitness) :=
  let clab := classId.label
  let newObj : Object clab := constr.created args
  let consumable : ConsumableObject clab :=
      { object := newObj
        ephemeral := true }
  let consumed : ConsumedObject classId.label := { consumable with can_nullify := Anoma.nullifyUniversal consumable.resource }
  let created : List CreatedObject :=
        [CreatedObject.fromSomeObject newObj.toSomeObject (ephemeral := false)]
  Action.create lab (.classMember (.constructorId constrId)) UUnit.unit args [consumed] created

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
  -- Note that this logic is triggered only for objects of the class described
  -- by `classId.label`. So `args.self` should always correspond a valid object
  -- of the class.
  let try selfObj : Object classId.label := Object.fromResource args.self
  let try argsData := SomeType.cast args.data.memberArgs
  method.invariant selfObj argsData
    && Logic.checkResourcesData [selfObj.toSomeObject] args.consumed
    && let createdObjects := method.created selfObj argsData
       Logic.checkResourcesData createdObjects args.created
    && Logic.checkResourcesPersistent args.consumed
    && Logic.checkResourcesPersistent args.created

def Method.action
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (methodId : classId.label.MethodId)
  (method : Class.Method methodId)
  (self : Object classId.label)
  (args : methodId.Args.type)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) := do
  let consumable : ConsumableObject classId.label :=
      { object := self
        ephemeral := false }
  let try consumed := consumable.consume
  let createObject (o : SomeObject) : CreatedObject :=
    { object := o.object
      ephemeral := false }
  let created : List CreatedObject :=
      List.map createObject (method.created self args)
  Action.create lab (.classMember (.methodId methodId)) UUnit.unit args [consumed] created

/-- Creates an Anoma Transaction for a given object method. -/
def Method.transaction
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (methodId : classId.label.MethodId)
  (method : Class.Method methodId)
  (self : Object classId.label)
  (args : methodId.Args.type)
  : Rand (Option Anoma.Transaction) := do
  let try (action, witness) ← method.action methodId self args
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
  let try argsData := SomeType.cast args.data.memberArgs
  let try selfObj : Object classId.label := Object.fromResource args.self
  Logic.checkResourcesData [selfObj.toSomeObject] args.consumed
    && Logic.checkResourcesData [selfObj.toSomeObject] args.created
    && Logic.checkResourcesPersistent args.consumed
    && Logic.checkResourcesEphemeral args.created
    && destructor.invariant selfObj argsData

def Destructor.action
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (destructorId : classId.label.DestructorId)
  (_destructor : Class.Destructor destructorId)
  (self : Object classId.label)
  (args : destructorId.Args.type)
  : Rand (Option (Anoma.Action × Anoma.DeltaWitness)) :=
  let consumable : ConsumableObject classId.label :=
       { object := self
         ephemeral := false }
  let try consumed := consumable.consume
  let createdObject : CreatedObject :=
    { object := self
      ephemeral := true }
  Action.create lab (.classMember (.destructorId destructorId)) UUnit.unit args [consumed] [createdObject]

/-- Creates an Anoma Transaction for a given object destructor. -/
def Destructor.transaction
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  (destructorId : classId.label.DestructorId)
  (destructor : Class.Destructor destructorId)
  (self : Object classId.label)
  (args : destructorId.Args.type)
  : Rand (Option Anoma.Transaction) := do
  let try (action, witness) ← destructor.action destructorId self args
  pure <|
    some
      { actions := [action],
        deltaProof := Anoma.Transaction.generateDeltaProof witness [action] }

/-- Creates a member logic for a given intent. This logic is checked when an
  object is consumed to create the intent. Note that the intent member logic
  (defined here) is distinct from the intent logic defined in
  `AVM/Intent/Translation.lean`. The intent member logic is associated with
  a resource consumed by the intent and it checks that the right intent is
  created. The intent logic is checked on consumption of the intent resource
  and it checks that the the intent's condition is satified. -/
def Intent.logic
  {lab : Ecosystem.Label}
  {ilab : Intent.Label}
  (_intent : Intent ilab)
  (args : Logic.Args lab)
  : Bool :=
  -- Check that exactly one resource is created that corresponds to the intent
  match Logic.filterOutDummy args.created with
  | [intentRes] =>
    let try labelData := Intent.LabelData.fromResource intentRes
    -- NOTE: We should also check that the intent logic hashes of
    -- `intentRes` and `intent` match.
    labelData.label === ilab
    && intentRes.quantity == 1
    && intentRes.ephemeral
    && Logic.checkResourcesData labelData.data.provided args.consumed
  | _ =>
    false

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
  : Bool :=
  let try selfObj : Object classId.label := Object.fromResource args.self
  let cls : Class classId := eco.classes classId
  cls.invariant selfObj args &&
  match memberId with
  | .constructorId c =>
    Constructor.logic (cls.constructors c) args
  | .methodId m =>
    Method.logic (cls.methods m) args
  | .destructorId m =>
    Destructor.logic (cls.destructors m) args
  | .intentId l =>
    if h : l ∈ classId.label.intentLabels then
      let intent : Intent l := cls.intents l h
      Intent.logic intent args
    else
      false
