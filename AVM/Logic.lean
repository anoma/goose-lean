import Prelude
import Anoma
import AVM.Object
import AVM.Message
import AVM.Action.DummyResource
import AVM.Logic.Base

namespace AVM.Logic

/-- Filters out dummy resources from a list of resources. -/
def filterOutDummy (resources : List Anoma.Resource) : List Anoma.Resource :=
  resources.filter (not ∘ Action.isDummyResource)

def resourceValueEq (objValue : ObjectValue) (res : Anoma.Resource) : Anoma.LogicM := Anoma.LogicM.withTrace here# "resourceValueEq" do
  docheck objValue.label === res.label
    failwith do
    have := res.Label.typeRepr
    Anoma.LogicM.throw here#
        s!"label mismatch:
        objValue: {repr objValue.label}
        resource: {repr res.label}"
  docheck objValue.classId.label.logicRef == res.logicRef
    failwith throw (.custom here# "logicRef")
  docheck objValue.data.quantity == res.quantity
    failwith throw (.custom here# "quantity")
  let try resVal : Object.Resource.Value objValue.classId := tryCast res.value
  docheck resVal.privateFields == objValue.data.privateFields
  docheck resVal.uid == objValue.uid
  Anoma.LogicM.true

def resourceIdEq (objValue : ObjectValue) (res : Anoma.Resource) : Bool :=
  let try resVal : Object.Resource.Value objValue.classId := tryCast res.value
  resVal.uid == objValue.uid

/-- Checks that the number of objects and resources match, and that the
    quantity, value and labels of each resource match the corresponding object.
    This check is used in the constructor, destructor and method message logics.
    Dummy resources in the `resources` list are ignored. -/
def checkResourceValues (objectValues : List ObjectValue) (resources : List Anoma.Resource) : Anoma.LogicM :=
  Anoma.LogicM.withTrace here# "checkResourceValues" do
  let resources' := Logic.filterOutDummy resources
  docheck objectValues.length == resources'.length
    failwith (throw (.custom here# "length"))
  List.zipWithM' resourceValueEq objectValues resources'

def checkResourcesEphemeral (resources : List Anoma.Resource) : Bool :=
  Logic.filterOutDummy resources |>.all Anoma.Resource.isEphemeral

def checkResourcesPersistent (resources : List Anoma.Resource) : Bool :=
  Logic.filterOutDummy resources |>.all Anoma.Resource.isPersistent

def selectObjectResources (resources : List Anoma.Resource) : List Anoma.Resource :=
  resources.filter Resource.isSomeObject

def selectMessageResources (resources : List Anoma.Resource) : List Anoma.Resource :=
  resources.filter Resource.isSomeMessage

def isObjectPreserved (obj : ObjectValue) (resources : List Anoma.Resource) : Bool :=
  let! [res] := resources.filter (resourceIdEq obj)
  (resourceValueEq obj res).isOk && res.isPersistent
