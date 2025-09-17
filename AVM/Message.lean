import AVM.Class.Label
import AVM.Ecosystem.Label
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
  recipients : List.Vector ObjectId id.numObjectArgs

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
                  recipients := List.Vector.singleton 0 }}

def Message.toSomeMessage {lab : Ecosystem.Label} (msg : Message lab) : SomeMessage :=
  { label := lab, message := msg }

instance Message.coeToSomeMessage {lab : Ecosystem.Label} : CoeHead (Message lab) SomeMessage where
  coe := toSomeMessage

def SomeMessage.toResource (msg : SomeMessage) (nonce : Anoma.Nonce) : Anoma.Resource :=
  { Val := ⟨PUnit⟩,
    Label := ⟨SomeMessage⟩,
    label := msg,
    logicRef := msg.message.logicRef,
    value := PUnit.unit,
    quantity := 1,
    nullifierKeyCommitment := default,
    ephemeral := true,
    nonce }

def SomeMessage.fromResource (res : Anoma.Resource.{u, v}) : Option SomeMessage :=
  let try msg : SomeMessage := tryCast res.label
  check (msg.message.logicRef == res.logicRef)
  some msg

def Message.toResource {lab : Ecosystem.Label} (msg : Message lab) (nonce : Anoma.Nonce) : Anoma.Resource :=
  msg.toSomeMessage.toResource nonce

def Message.fromResource {lab : Ecosystem.Label} (res : Anoma.Resource) : Option (Message lab) :=
  let try smsg : SomeMessage := SomeMessage.fromResource res
  tryCast smsg.message

def Resource.isSomeMessage (res : Anoma.Resource) : Bool :=
  match SomeMessage.fromResource res with
  | some _ => true
  | none => false
