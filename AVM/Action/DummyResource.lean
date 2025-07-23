
import Prelude
import Anoma

namespace AVM.Action

/-- A dummy resource used in generated actions. -/
def dummyResource (nonce : Anoma.Nonce) : Anoma.Resource.{u, v} :=
  { Val := ⟨UUnit.{u}⟩,
    Label := ⟨ULift.{v} String⟩,
    label := ULift.up.{v} "dummy-resource",
    quantity := 0,
    value := UUnit.unit,
    ephemeral := true,
    nonce,
    nullifierKeyCommitment := Anoma.NullifierKeyCommitment.universal }

/-- Checks if a resource is a dummy resource. -/
def isDummyResource (res : Anoma.Resource.{u, v}) : Bool :=
  res.label === ULift.up.{v} "dummy-resource" && res.ephemeral && res.quantity == 0

/-- The resource logic of any dummy resource. -/
def dummyResourceLogic (args : Anoma.Logic.Args.{u, v} Unit) : Bool :=
  let res : Anoma.Resource.{u, v} := args.self
  isDummyResource res
