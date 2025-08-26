import Prelude
import Anoma
import AVM.Object
import AVM.Message
import AVM.Action.DummyResource

namespace AVM.Logic

/-- Filters out dummy resources from a list of resources. -/
def filterOutDummy (resources : List Anoma.Resource.{u, v}) : List Anoma.Resource.{u, v} :=
  resources.filter (not ∘ Action.isDummyResource)

/-- Checks that the number of objects and resources match, and that the
    resources' quantity, value and labels match the objects' data and labels.
    This check is used in the constructor and method message logics. Dummy resources
    in the `resources` list are ignored. -/
def checkResourcesData (objectData : List SomeObjectData) (resources : List Anoma.Resource) : Bool :=
  let resources' := Logic.filterOutDummy resources
  objectData.length == resources'.length
    && List.and (List.zipWith resourceDataEq objectData resources')
  where
    resourceDataEq (sdata : SomeObjectData) (res : Anoma.Resource) : Bool :=
      -- NOTE: We should check the whole resource kind (label + logic) instead
      -- of checking just the label. We should also check that the intent logic
      -- hashes of `sobj` and `res` match.
      sdata.label === res.label &&
      sdata.data.quantity == res.quantity &&
        let try privateFields := tryCast sdata.data.privateFields
        res.value == privateFields

def checkResourcesEphemeral (resources : List Anoma.Resource) : Bool :=
  Logic.filterOutDummy resources |>.all Anoma.Resource.isEphemeral

def checkResourcesPersistent (resources : List Anoma.Resource) : Bool :=
  Logic.filterOutDummy resources |>.all Anoma.Resource.isPersistent

def selectObjectResources.{u, v} (resources : List Anoma.Resource.{u, v}) : List Anoma.Resource.{u, v} :=
  resources.filter Resource.isSomeObject.{u, v, v}

def selectMessageResources.{u, v} (resources : List Anoma.Resource.{u, v}) : List Anoma.Resource.{u, v} :=
  resources.filter Resource.isSomeMessage
