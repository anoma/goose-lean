import Prelude
import Anoma

namespace AVM.Action

private def dummyResourceLabel.{u} : ULift.{u} String :=
  ULift.up.{u} "dummy-resource"

private def dummyResourceLogicRef : Anoma.LogicRef :=
  ⟨"dummy-resource-logic"⟩

/-- Checks if a resource is a dummy resource. -/
def isDummyResource (res : Anoma.Resource.{u, v}) : Bool :=
  res.label === dummyResourceLabel.{v} &&
  res.logicRef == dummyResourceLogicRef &&
  res.ephemeral &&
  res.quantity == 0

/-- The resource logic of any dummy resource. -/
private def dummyResourceLogic : Anoma.Logic.{u, v} :=
  { reference := dummyResourceLogicRef,
    function :=
      fun (args : Anoma.Logic.Args.{u, v}) =>
        let res : Anoma.Resource.{u, v} := args.self
        isDummyResource res }

/-- A dummy resource used in generated actions. -/
def dummyResource.{u, v} (nonce : Anoma.Nonce) : Anoma.Resource.{u, v} :=
  { Val := ⟨PUnit.{u + 1}⟩,
    Label := ⟨ULift.{v} String⟩,
    label := dummyResourceLabel.{v},
    logicRef := dummyResourceLogic.{u, v}.reference,
    quantity := 0,
    value := PUnit.unit,
    ephemeral := true,
    nonce,
    nullifierKeyCommitment := Anoma.NullifierKeyCommitment.universal }
