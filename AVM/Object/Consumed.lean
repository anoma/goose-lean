import Anoma.Resource
import AVM.Class.Label
import AVM.Object

namespace AVM

structure ConsumableObject {lab : Ecosystem.Label} (classId : lab.ClassId) where
  object : Object classId
  ephemeral : Bool
  deriving BEq

structure SomeConsumableObject where
  {label : Ecosystem.Label}
  {classId : label.ClassId}
  consumable : ConsumableObject classId

def SomeObject.toConsumable (ephemeral : Bool) (sobj : SomeObject) : SomeConsumableObject :=
  { label := sobj.label
    consumable :=
     { object := sobj.object
       ephemeral }}

def ConsumableObject.toResource {lab : Ecosystem.Label} {c : lab.ClassId} (c : ConsumableObject c) : Anoma.Resource :=
  c.object.toResource c.ephemeral

structure ConsumedObject {lab : Ecosystem.Label} (c : lab.ClassId) extends ConsumableObject c where
  can_nullify : Anoma.CanNullifyResource Anoma.NullifierKey.universal (object.toResource ephemeral)

def ConsumedObject.toConsumable {lab : Ecosystem.Label} {c : lab.ClassId} (o : ConsumedObject c) : ConsumableObject c :=
 { object := o.object
   ephemeral := o.ephemeral }

instance ConsumedObject.instBEq {lab : Ecosystem.Label} {c : lab.ClassId}: BEq (ConsumedObject c) where
  beq a b := BEq.beq a.toConsumable b.toConsumable

instance ConsumedObject.hasTypeRep (lab : Ecosystem.Label) {c : lab.ClassId} : TypeRep (ConsumedObject c) where
  rep := Rep.composite "AVM.ConsumedObject" [Rep.atomic lab.name, Rep.atomic c.label.name]

structure SomeConsumedObject where
  {label : Ecosystem.Label}
  {classId : label.ClassId}
  consumed : ConsumedObject classId

instance SomeConsumedObject.hasBEq : BEq SomeConsumedObject where
  beq a b :=
    a.label === b.label
    && a.classId.label == b.classId.label
    && a.consumed === b.consumed

instance SomeConsumedObject.hasTypeRep : TypeRep SomeConsumedObject where
  rep := Rep.atomic "AVM.SomeConsumedObject"

def ConsumedObject.toSomeConsumedObject {lab : Ecosystem.Label} {c : lab.ClassId} (o : ConsumedObject c) : SomeConsumedObject := ⟨o⟩

instance ConsumedObject.coeToSomeConsumedObject {lab : Ecosystem.Label} {c : lab.ClassId} : CoeHead (ConsumedObject c) SomeConsumedObject where
  coe := toSomeConsumedObject

def Object.toConsumable {lab : Ecosystem.Label} {c : lab.ClassId} (object : Object c) (ephemeral : Bool) : ConsumableObject c where
  object
  ephemeral

def ConsumableObject.consume {lab : Ecosystem.Label} {c : lab.ClassId} (o : ConsumableObject c) : Option (ConsumedObject c) :=
  let resource := o.toResource
  match resource.nullify Anoma.NullifierKey.universal with
  | isFalse _ => none
  | isTrue can_nullify => pure
       { object := o.object
         ephemeral := o.ephemeral
         can_nullify }

def SomeConsumableObject.toSomeObject (c : SomeConsumableObject) : SomeObject :=
  c.consumable.object.toSomeObject

def SomeConsumableObject.consume (c : SomeConsumableObject) : Option SomeConsumedObject :=
  let try consumed := c.consumable.consume
  some { label := c.label, consumed }

def SomeConsumedObject.toSomeObject (sconsumed : SomeConsumedObject) : SomeObject :=
  ⟨sconsumed.consumed.object⟩

def SomeObject.toConsumedObject (ephemeral : Bool) (sobj : SomeObject) : Option SomeConsumedObject :=
  sobj.toConsumable ephemeral |>.consume

def Object.toConsumedObject {lab : Ecosystem.Label} {c : lab.ClassId} (ephemeral : Bool) (obj : Object c) : Option SomeConsumedObject :=
  SomeObject.toConsumedObject ephemeral obj.toSomeObject
