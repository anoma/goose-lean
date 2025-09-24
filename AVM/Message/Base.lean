import AVM.Ecosystem.Data

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
  recipients : List ObjectId

instance Message.hasTypeRep (lab : Ecosystem.Label) : TypeRep (Message lab) where
  rep := Rep.composite "AVM.Message" [Rep.atomic lab.name]

instance Message.hasBEq {lab : Ecosystem.Label} : BEq (Message lab) where
  beq a b :=
    a.id == b.id
    && a.vals === b.vals
    && a.args === b.args
    && a.recipients ≍? b.recipients

structure SomeMessage : Type 1 where
  {label : Ecosystem.Label}
  message : Message label

instance SomeMessage.hasTypeRep : TypeRep SomeMessage where
  rep := Rep.atomic "AVM.SomeMessage"

instance SomeMessage.hasBEq : BEq SomeMessage where
  beq a b := a.label == b.label && a.message === b.message

instance : Inhabited SomeMessage where
  default := { label := Ecosystem.Label.dummy
               message :=
                { Vals := ⟨PUnit⟩
                  vals := PUnit.unit
                  data := .unit
                  logicRef := default
                  id := .classMember (classId := .unit) (.constructorId PUnit.unit),
                  args := PUnit.unit
                  recipients := [] }}

def Message.toSomeMessage {lab : Ecosystem.Label} (msg : Message lab) : SomeMessage :=
  { label := lab, message := msg }

instance Message.coeToSomeMessage {lab : Ecosystem.Label} : CoeHead (Message lab) SomeMessage where
  coe := toSomeMessage
