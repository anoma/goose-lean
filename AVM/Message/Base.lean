import AVM.Ecosystem.Label

namespace AVM

/-- A message is a communication sent from one object to another in the AVM. -/
structure Message (lab : Ecosystem.Label) : Type 1 where
  {Vals : SomeType.{0}}
  /-- Message parameter values. The message parameters are object resources and
    generated random values that are used in the body of the call associated with
    the message. These need to be provided in the message, because the
    associated Resource Logic cannot fetch object resources from the Anoma
    system or generate new object identifiers. -/
  vals : Vals.type
  /-- Resource logic reference for the message logic. -/
  logicRef : Anoma.LogicRef
  /-- The message ID. -/
  id : lab.MemberId
  /-- The arguments of the message. -/
  args : id.Args.type
  /-- Extra data. -/
  data : id.Data
  /-- The recipients of the message. -/
  recipients : List.Vector ObjectId id.numObjectArgs

instance Message.hasTypeRep (lab : Class.Label) : TypeRep (Message lab) where
  rep := Rep.composite "AVM.Message" [Rep.atomic lab.name]

instance Message.hasBEq {lab : Class.Label} : BEq (Message lab) where
  beq a b :=
    a.id == b.id
    && a.vals === b.vals
    && a.args === b.args
    && a.recipient == b.recipient

structure SomeMessage where
  {label : Class.Label}
  message : Message label

instance SomeMessage.hasTypeRep : TypeRep SomeMessage where
  rep := Rep.atomic "AVM.SomeMessage"

instance SomeMessage.hasBEq : BEq SomeMessage where
  beq a b := a.label == b.label && a.message === b.message

instance : Inhabited SomeMessage where
  default := { label := Class.Label.dummy, message := { Vals := ⟨PUnit⟩, vals := PUnit.unit, logicRef := default, id := .constructorId PUnit.unit, args := PUnit.unit, recipient := 0 } }

def Message.toSomeMessage {lab : Class.Label} (msg : Message lab) : SomeMessage :=
  { label := lab, message := msg }

instance Message.coeToSomeMessage {lab : Class.Label} : CoeHead (Message lab) SomeMessage where
  coe := toSomeMessage
