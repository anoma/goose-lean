import Prelude
import Anoma
import AVM.Object

-- TODO rename to Resource.dummy?
def dummyResource (nonce : Anoma.Nonce) : Anoma.Resource.{u, v} :=
  { Val := ⟨UUnit⟩,
    Label := ⟨ULift String⟩,
    label := ULift.up "dummy-resource",
    quantity := 0,
    value := UUnit.unit,
    ephemeral := true,
    nonce,
    nullifierKeyCommitment := Anoma.NullifierKeyCommitment.universal }

namespace AVM.Logic

def filterOutDummy (resources : List Anoma.Resource.{u, v}) : List Anoma.Resource.{u, v} :=
  resources.filter (fun res => res.label !== ULift.up.{v} "dummy-resource")

/-- Checks that the number of objects and resources match, and that the
    resources' private data and labels match the objects' private data and
    labels. This check is used in the constructor and method logics. Dummy
    resources in the `resources` list are ignored. -/
def checkResourceData (objects : List SomeObject) (resources : List Anoma.Resource) : Bool :=
  let resources' := Logic.filterOutDummy resources
  objects.length == resources'.length
    && List.and (List.zipWith resourceDataEq objects resources')
  where
    resourceDataEq (sobj : SomeObject) (res : Anoma.Resource) : Bool :=
      -- NOTE: We should check the whole resource kind (label + logic) instead
      -- of checking just the label. We should also check that the intent logic
      -- hashes of `sobj.object` and `res` match.
      sobj.label === res.label &&
      sobj.object.nullifierKeyCommitment == res.nullifierKeyCommitment &&
      sobj.object.quantity == res.quantity &&
        let try privateFields := tryCast sobj.object.privateFields
        res.value == privateFields
