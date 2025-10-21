import AVM.Message.Data
import AVM.Authorization

namespace AVM

/-- A message is a communication sent from one object to another in the AVM. -/
structure Message (lab : Ecosystem.Label) : Type 1 where
  data : MessageData lab
  /-- Signatures for `data`. -/
  signatures : List Signature

instance {lab : Ecosystem.Label} : Repr (Message lab) where
  reprPrec r _ :=
    have := r.Vals.typeRepr
    have := r.id.Args.typeRepr
    s!"Message@\{
      id := {repr r.id}
      vals := {repr r.vals}
      args := {repr r.args}
      logicRef := {repr r.logicRef}
      recipients := {repr r.recipients}
    }"

def Message.rawSignatures {lab : Ecosystem.Label} (msg : Message lab) : List Nat :=
  msg.signatures.map Signature.raw

instance Message.instHashable (lab : Ecosystem.Label) : Hashable (Message lab) where
  hash m := Hashable.Mix.run do
    mix m.data.id

instance Message.hasTypeRep (lab : Ecosystem.Label) : TypeRep (Message lab) where
  rep := Rep.composite "AVM.Message" [Rep.atomic lab.name]

instance Message.hasBEq {lab : Ecosystem.Label} : BEq (Message lab) where
  beq a b :=
    a.data == b.data && a.rawSignatures == b.rawSignatures

structure SomeMessage : Type 1 where
  {label : Ecosystem.Label}
  message : Message label

instance SomeMessage.instRepr : Repr SomeMessage where
  reprPrec m _ := repr m.message

instance SomeMessage.instHashable : Hashable SomeMessage where
  hash m := Hashable.Mix.run do
    mix m.label
    mix m.message

instance SomeMessage.hasTypeRep : TypeRep SomeMessage where
  rep := Rep.atomic "AVM.SomeMessage"

instance SomeMessage.hasBEq : BEq SomeMessage where
  beq a b := a.label == b.label && a.message === b.message

instance : Inhabited SomeMessage where
  default := { label := Ecosystem.Label.dummy
               message :=
                { data :=
                    { id := .classMember (classId := .unit) (.constructorId PUnit.unit)
                      Vals := ⟨PUnit⟩
                      vals := PUnit.unit
                      args := PUnit.unit
                      recipients := [] },
                  signatures := [] }}

def Message.toSomeMessage {lab : Ecosystem.Label} (msg : Message lab) : SomeMessage :=
  { label := lab, message := msg }

instance Message.coeToSomeMessage {lab : Ecosystem.Label} : CoeHead (Message lab) SomeMessage where
  coe := toSomeMessage
