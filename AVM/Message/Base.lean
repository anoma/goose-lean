import AVM.Ecosystem.Data

namespace AVM

/-- A message is a communication sent from one object to another in the AVM. -/
structure Message (lab : Ecosystem.Label) : Type 1 where
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
  /-- The signature of the arguments -/
  signatures : id.Signatures args

def Message.rawSignatures {lab : Ecosystem.Label} (msg : Message lab) : List Nat :=
  let {id := id, signatures := signatures, ..} := msg
  match id with
  | .multiMethodId m => lab.MultiMethodSignatureIdEnum m |>.toList.map (fun s => signatures s |>.raw)
  | .classMember (classId := clab) c => match c with
    | .methodId m => clab.label.MethodSignatureIdEnum m |>.toList.map (fun s => signatures s |>.raw)
    | .destructorId m => clab.label.DestructorSignatureIdEnum m |>.toList.map (fun s => signatures s |>.raw)
    | .constructorId m => clab.label.ConstructorSignatureIdEnum m |>.toList.map (fun s => signatures s |>.raw)
    | .upgradeId => []

instance Message.hasTypeRep (lab : Ecosystem.Label) : TypeRep (Message lab) where
  rep := Rep.composite "AVM.Message" [Rep.atomic lab.name]

instance Message.hasBEq {lab : Ecosystem.Label} : BEq (Message lab) where
  beq a b :=
    let {id := aid, args := aargs, signatures := asigs, ..} := a
    let {id := bid, args := bargs, signatures := bsigs, ..} := b
    check h : aid == bid
    let h' := eq_of_beq h
    check a.vals === b.vals
    check s : aargs == cast (by simp! [h']) bargs
    check a.recipients == b.recipients
    check a.rawSignatures == b.rawSignatures

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
                { id := .classMember (classId := .unit) (.constructorId PUnit.unit)
                  Vals := ⟨PUnit⟩
                  vals := PUnit.unit
                  logicRef := default
                  signatures f := nomatch f
                  args := PUnit.unit
                  recipients := [] }}

def Message.toSomeMessage {lab : Ecosystem.Label} (msg : Message lab) : SomeMessage :=
  { label := lab, message := msg }

instance Message.coeToSomeMessage {lab : Ecosystem.Label} : CoeHead (Message lab) SomeMessage where
  coe := toSomeMessage
