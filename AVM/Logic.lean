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
    quantity, value and labels of each resource match the corresponding object.
    This check is used in the constructor, destructor and method message logics.
    Dummy resources in the `resources` list are ignored. -/
def checkResourceValues (objectValues : List ObjectValue) (resources : List Anoma.Resource) : Bool :=
  let resources' := Logic.filterOutDummy resources
  objectValues.length == resources'.length
    && List.and (List.zipWith resourceValueEq objectValues resources')
  where
    resourceValueEq (sdata : ObjectValue) (res : Anoma.Resource) : Bool :=
      sdata.label === res.label &&
      sdata.label.logicRef == res.logicRef &&
      sdata.data.quantity == res.quantity &&
        let try resVal : Object.Resource.Value sdata.label := tryCast res.value
        resVal.privateFields == sdata.data.privateFields &&
        resVal.uid == sdata.uid

def checkResourcesEphemeral (resources : List Anoma.Resource) : Bool :=
  Logic.filterOutDummy resources |>.all Anoma.Resource.isEphemeral

def checkResourcesPersistent (resources : List Anoma.Resource) : Bool :=
  Logic.filterOutDummy resources |>.all Anoma.Resource.isPersistent

def selectObjectResources.{u, v} (resources : List Anoma.Resource.{u, v}) : List Anoma.Resource.{u, v} :=
  resources.filter Resource.isSomeObject.{u, v, v}

def selectMessageResources.{u, v} (resources : List Anoma.Resource.{u, v}) : List Anoma.Resource.{u, v} :=
  resources.filter Resource.isSomeMessage
