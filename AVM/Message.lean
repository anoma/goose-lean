import AVM.Class.Label
import AVM.Ecosystem.Label
import AVM.Ecosystem.Data
import AVM.Authorization
import AVM.Logic.Base

namespace AVM

def SomeMessage.fromResource (res : Anoma.Resource) : Option SomeMessage :=
  let try msg : SomeMessage := tryCast res.label
  some msg

private def messageResourceLogicRef : Anoma.LogicRef :=
  ⟨"message-resource-logic"⟩

def Message.logicfun (args : Anoma.Logic.Args) : Anoma.LogicM :=
  match args.status with
  | Created => .true
  | Consumed => do
    let try self : SomeMessage := SomeMessage.fromResource args.self
    let allObjectUids : Std.HashSet ObjectId :=
        args.consumed
          |> selectObjects
          |>.map (·.object.uid)
          |> Std.HashSet.ofList
    forM self.message.data.recipients fun recipient => do
      docheck recipient ∈ allObjectUids
        failwith (Anoma.LogicM.throw here# s!"recipient {repr recipient} not in Action")
      Anoma.LogicM.true

def messageResourceLogic : Anoma.Logic :=
  { reference := messageResourceLogicRef,
    function := Message.logicfun }

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

def Message.toResource {lab : Ecosystem.Label} (msg : Message lab) (nonce : Anoma.Nonce) : Anoma.Resource :=
  msg.toSomeMessage.toResource nonce

def Message.fromResource {lab : Ecosystem.Label} (res : Anoma.Resource) : Option (Message lab) :=
  let try smsg : SomeMessage := SomeMessage.fromResource res
  tryCast smsg.message

def Resource.isSomeMessage (res : Anoma.Resource) : Bool :=
  Option.isSome (SomeMessage.fromResource res)

def Message.checkSignature {lab : Ecosystem.Label} (msg : Message lab) (pub : PublicKey)  : Bool :=
  AVM.checkSignature msg.data msg.signatures pub
