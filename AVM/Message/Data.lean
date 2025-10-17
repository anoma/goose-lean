import AVM.Ecosystem.Data

namespace AVM

/-- A message is a communication sent from one object to another in the AVM. -/
structure MessageData (lab : Ecosystem.Label) : Type 1 where
  /-- The message ID. -/
  id : lab.MemberId
  {Vals : SomeType.{0}}
  /-- Message parameter values. The message parameters are object resources and
    generated random values that are used in the body of the call associated with
    the message. These need to be provided in the message, because the
    associated Resource Logic cannot fetch object resources from the Anoma
    system or generate new object identifiers. -/
  vals : Vals.type
  /-- Resource logic reference for the message logic. -/
  logicRef : Anoma.LogicRef
  /-- The arguments of the message. -/
  args : id.Args.type
  /-- The recipients of the message. -/
  recipients : List ObjectId

instance MessageData.hasTypeRep (lab : Ecosystem.Label) : TypeRep (MessageData lab) where
  rep := Rep.composite "AVM.MessageData" [Rep.atomic lab.name]

instance MessageData.hasBEq {lab : Ecosystem.Label} : BEq (MessageData lab) where
  beq a b :=
    let {id := aid, args := aargs, ..} := a
    let {id := bid, args := bargs, ..} := b
    check h : aid == bid
    let h' := eq_of_beq h
    check a.vals === b.vals
    check s : aargs == cast (by simp! [h']) bargs
    check a.recipients == b.recipients
