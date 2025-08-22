import Anoma.Resource
import AVM.Class.Label
import AVM.Object

namespace AVM

structure ConsumableObject (lab : Class.Label) where
  object : Object lab
  ephemeral : Bool
  deriving BEq

structure SomeConsumableObject where
  {label : Class.Label}
  consumable : ConsumableObject label

def SomeObject.toConsumable (ephemeral : Bool) (sobj : SomeObject) : SomeConsumableObject :=
  { label := sobj.label
    consumable :=
     { object := sobj.object
       ephemeral }}

def ConsumableObject.toResource {lab : Class.Label} (c : ConsumableObject lab) : Anoma.Resource :=
  c.object.toResource c.ephemeral c.object.nonce

structure ConsumedObject (lab : Class.Label) extends ConsumableObject lab where
  can_nullify : Anoma.CanNullifyResource Anoma.NullifierKey.universal (object.toResource ephemeral object.nonce)

def ConsumedObject.toConsumable {lab : Class.Label} (c : ConsumedObject lab) : ConsumableObject lab :=
 { object := c.object
   ephemeral := c.ephemeral }

instance ConsumedObject.instBEq {lab : Class.Label} : BEq (ConsumedObject lab) where
  beq a b := BEq.beq a.toConsumable b.toConsumable

instance ConsumedObject.hasTypeRep (lab : Class.Label) : TypeRep (ConsumedObject lab) where
  rep := Rep.composite "AVM.ConsumedObject" [Rep.atomic lab.name]

structure SomeConsumedObject where
  {label : Class.Label}
  consumed : ConsumedObject label

instance SomeConsumedObject.hasBEq : BEq SomeConsumedObject where
  beq a b := a.label === b.label && a.consumed === b.consumed

instance SomeConsumedObject.hasTypeRep : TypeRep SomeConsumedObject where
  rep := Rep.atomic "AVM.SomeConsumedObject"

def ConsumedObject.toSomeConsumedObject {lab : Class.Label} (c : ConsumedObject lab) : SomeConsumedObject := ⟨c⟩

instance ConsumedObject.coeToSomeConsumedObject {lab : Class.Label} : CoeHead (ConsumedObject lab) SomeConsumedObject where
  coe := toSomeConsumedObject

def Object.toConsumable {lab : Class.Label} (object : Object lab) (ephemeral : Bool) : ConsumableObject lab where
  object
  ephemeral

def ConsumableObject.consume {lab : Class.Label} (c : ConsumableObject lab) : Option (ConsumedObject lab) :=
  let resource := c.toResource
  match resource.nullify Anoma.NullifierKey.universal with
  | isFalse _ => none
  | isTrue can_nullify => pure
       { object := c.object
         ephemeral := c.ephemeral
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

def Object.toConsumedObject {lab : Class.Label} (ephemeral : Bool) (obj : Object lab) : Option SomeConsumedObject :=
  SomeObject.toConsumedObject ephemeral obj.toSomeObject
