import AVM.Class.Label

namespace AVM

/-- A message is a communication sent from one object to another in the AVM. -/
structure Message.{u} (lab : Class.Label.{u}) : Type (u + 1) where
  {Vals : SomeType}
  /-- Message parameter values. The message parameters are object resources and
    generated object ids that are used in the body of the call associated with
    the message. These need to be provided in the message, because the
    associated Resource Logic cannot fetch object resources from the Anoma
    system or generate new object identifiers. -/
  vals : Vals.type
  /-- The message ID. -/
  id : Class.Label.MemberId lab
  /-- The arguments of the message. -/
  args : (Class.Label.MemberId.Args.{u} id).type
  /-- The recipient of the message. -/
  recipient : ObjectId

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
  default := { label := Class.Label.dummy, message := { Vals := ⟨PUnit⟩, vals := PUnit.unit, id := .constructorId PUnit.unit, args := PUnit.unit, recipient := 0 } }

def Message.toSomeMessage {lab : Class.Label} (msg : Message lab) : SomeMessage :=
  { label := lab, message := msg }

instance Message.coeToSomeMessage {lab : Class.Label} : CoeHead (Message lab) SomeMessage where
  coe := toSomeMessage

def SomeMessage.toResource (msg : SomeMessage) (nonce : Anoma.Nonce) : Anoma.Resource :=
  { Val := ⟨PUnit⟩,
    Label := ⟨SomeMessage⟩,
    value := PUnit.unit,
    quantity := 1,
    label := msg,
    nullifierKeyCommitment := default,
    ephemeral := true,
    nonce }

def SomeMessage.fromResource (res : Anoma.Resource.{u, v}) : Option SomeMessage.{v} :=
  tryCast res.label

def Message.toResource {lab : Class.Label} (msg : Message lab) (nonce : Anoma.Nonce) : Anoma.Resource :=
  msg.toSomeMessage.toResource nonce

def Message.fromResource {lab : Class.Label} (res : Anoma.Resource) : Option (Message lab) :=
  let try smsg : SomeMessage := SomeMessage.fromResource res
  tryCast smsg.message

def Resource.isSomeMessage (res : Anoma.Resource) : Bool :=
  match SomeMessage.fromResource res with
  | some _ => true
  | none => false
