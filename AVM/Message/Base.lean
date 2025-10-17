import AVM.Message.Data
import AVM.Authorization

namespace AVM

/-- A message is a communication sent from one object to another in the AVM. -/
structure Message (lab : Ecosystem.Label) : Type 1 where
  data : MessageData lab
  /-- The signature of the arguments -/
  signatures : data.id.SignatureId → Signature

def Message.rawSignatures {lab : Ecosystem.Label} (msg : Message lab) : List Nat :=
  let {data := {id := id, ..}, signatures := signatures, ..} := msg
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
    a.data == b.data && a.rawSignatures == b.rawSignatures

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
                { data :=
                    { id := .classMember (classId := .unit) (.constructorId PUnit.unit)
                      Vals := ⟨PUnit⟩
                      vals := PUnit.unit
                      logicRef := default
                      args := PUnit.unit
                      recipients := [] },
                  signatures f := nomatch f }}

def Message.toSomeMessage {lab : Ecosystem.Label} (msg : Message lab) : SomeMessage :=
  { label := lab, message := msg }

instance Message.coeToSomeMessage {lab : Ecosystem.Label} : CoeHead (Message lab) SomeMessage where
  coe := toSomeMessage
