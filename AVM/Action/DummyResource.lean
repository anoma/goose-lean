import Prelude
import Anoma

namespace AVM.Action

private def dummyResourceLabel : ULift.{1} String :=
  ULift.up "dummy-resource"

private def dummyResourceLogicRef : Anoma.LogicRef :=
  ⟨"dummy-resource-logic"⟩

/-- Checks if a resource is a dummy resource. -/
def isDummyResource (res : Anoma.Resource) : Bool :=
  res.label === dummyResourceLabel &&
  res.logicRef == dummyResourceLogicRef &&
  res.ephemeral &&
  res.quantity == 0

/-- The resource logic of any dummy resource. -/
private def dummyResourceLogic : Anoma.Logic :=
  { reference := dummyResourceLogicRef,
    function :=
      fun (args : Anoma.Logic.Args) =>
        let res : Anoma.Resource := args.self
        check isDummyResource res
        pure .unit }

/-- A dummy resource used in generated actions. -/
def dummyResource (nonce : Anoma.Nonce) : Anoma.Resource :=
  { Val := ⟨PUnit⟩,
    Label := ⟨ULift String⟩,
    label := dummyResourceLabel,
    logicRef := dummyResourceLogic.reference,
    quantity := 0,
    value := PUnit.unit,
    ephemeral := true,
    nonce,
    nullifierKeyCommitment := Anoma.NullifierKeyCommitment.universal }
