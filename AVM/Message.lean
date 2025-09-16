import AVM.Message.Base
import AVM.Label

namespace AVM

def SomeMessage.toResource (msg : SomeMessage) (nonce : Anoma.Nonce) : Anoma.Resource :=
  { Val := ⟨PUnit⟩,
    Label := ⟨Resource.Label⟩,
    label := Resource.Label.message msg,
    logicRef := msg.message.logicRef,
    value := PUnit.unit,
    quantity := 1,
    nullifierKeyCommitment := default,
    ephemeral := true,
    nonce }

def SomeMessage.fromResource (res : Anoma.Resource.{u, v}) : Option SomeMessage :=
  let try resLab : AVM.Resource.Label := tryCast res.label
  let try msg : SomeMessage := Resource.Label.getMessage resLab
  check (msg.message.logicRef == res.logicRef)
  some msg

def Message.toResource {lab : Ecosystem.Label} (msg : Message lab) (nonce : Anoma.Nonce) : Anoma.Resource :=
  msg.toSomeMessage.toResource nonce

def Message.fromResource {lab : Ecosystem.Label} (res : Anoma.Resource) : Option (Message lab) :=
  let try smsg : SomeMessage := SomeMessage.fromResource res
  tryCast smsg.message

def Resource.isSomeMessage (res : Anoma.Resource) : Bool :=
  Option.isSome (SomeMessage.fromResource res)
