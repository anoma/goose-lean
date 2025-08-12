import AVM.Class.Label

namespace AVM

structure Message.{u} (lab : Class.Label.{u}) : Type (u + 1) where
  /-- The message ID. -/
  id : Class.Label.MemberId lab
  /-- The arguments of the message. -/
  args : (Class.Label.MemberId.Args.{u} id).type
  /-- The sender of the message. -/
  sender : Anoma.ObjectId
  /-- The recipient of the message. -/
  recipient : Anoma.ObjectId

instance Message.hasTypeRep (lab : Class.Label) : TypeRep (Message lab) where
  rep := Rep.composite "AVM.Message" [Rep.atomic lab.name]

instance Message.hasBEq {lab : Class.Label} : BEq (Message lab) where
  beq a b :=
    a.id == b.id
    && a.args === b.args
    && a.sender == b.sender
    && a.recipient == b.recipient

def Message.toResource {lab : Class.Label} (msg : Message lab) (nonce : Anoma.Nonce) : Anoma.Resource :=
  { Val := ⟨PUnit⟩,
    Label := ⟨Message lab⟩,
    value := PUnit.unit,
    quantity := 1,
    label := msg,
    nullifierKeyCommitment := default,
    ephemeral := true,
    nonce }

structure SomeMessage where
  {label : Class.Label}
  message : Message label

instance SomeMessage.hasTypeRep : TypeRep SomeMessage where
  rep := Rep.atomic "AVM.SomeMessage"

instance SomeMessage.hasBEq : BEq SomeMessage where
  beq a b := a.label == b.label && a.message === b.message

def Message.toSomeMessage {lab : Class.Label} (msg : Message lab) : SomeMessage :=
  { label := lab, message := msg }

instance Message.coeToSomeMessage {lab : Class.Label} : CoeHead (Message lab) SomeMessage where
  coe := toSomeMessage

def SomeMessage.toResource (msg : SomeMessage) (nonce : Anoma.Nonce) : Anoma.Resource :=
  msg.message.toResource nonce
