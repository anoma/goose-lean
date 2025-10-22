import AVM.Class.Label
import AVM.Ecosystem.Label
import AVM.Ecosystem.Data
import AVM.Authorization
import AVM.Logic.Base

namespace AVM

def SomeMessage.toResource (msg : SomeMessage) (nonce : Anoma.Nonce) : Anoma.Resource :=
  { Val := ⟨PUnit⟩,
    Label := ⟨SomeMessage⟩,
    label := msg,
    logicRef := Logic.trivialLogicRef,
    value := PUnit.unit,
    quantity := 1,
    nullifierKeyCommitment := default,
    ephemeral := true,
    nonce }

def SomeMessage.fromResource (res : Anoma.Resource) : Option SomeMessage :=
  let try msg : SomeMessage := tryCast res.label
  some msg

def Message.toResource {lab : Ecosystem.Label} (msg : Message lab) (nonce : Anoma.Nonce) : Anoma.Resource :=
  msg.toSomeMessage.toResource nonce

def Message.fromResource {lab : Ecosystem.Label} (res : Anoma.Resource) : Option (Message lab) :=
  let try smsg : SomeMessage := SomeMessage.fromResource res
  tryCast smsg.message

def Resource.isSomeMessage (res : Anoma.Resource) : Bool :=
  Option.isSome (SomeMessage.fromResource res)

def Message.checkSignature {lab : Ecosystem.Label} (msg : Message lab) (pub : PublicKey)  : Bool :=
  AVM.checkSignature msg.data msg.signatures pub
