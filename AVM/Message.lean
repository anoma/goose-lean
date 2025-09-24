import AVM.Class.Label
import AVM.Ecosystem.Label
import AVM.Ecosystem.Data
import AVM.Authorization

namespace AVM

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
