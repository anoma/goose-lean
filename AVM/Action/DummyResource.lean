
import Prelude
import Anoma

namespace AVM.Action

private def dummyResourceLabel.{u} : ULift.{u} String :=
  ULift.up.{u} "dummy-resource"

/-- A dummy resource used in generated actions. -/
def dummyResource (nonce : Anoma.Nonce) : Anoma.Resource.{u, v} :=
  { Val := ⟨PUnit.{u + 1}⟩,
    Label := ⟨ULift.{v} String⟩,
    label := dummyResourceLabel.{v},
    quantity := 0,
    value := PUnit.unit,
    ephemeral := true,
    nonce,
    nullifierKeyCommitment := Anoma.NullifierKeyCommitment.universal }

/-- Checks if a resource is a dummy resource. -/
def isDummyResource (res : Anoma.Resource.{u, v}) : Bool :=
  res.label === dummyResourceLabel.{v} && res.ephemeral && res.quantity == 0

/-- The resource logic of any dummy resource. -/
def dummyResourceLogic (args : Anoma.Logic.Args.{u, v} Unit) : Bool :=
  let res : Anoma.Resource.{u, v} := args.self
  isDummyResource res
