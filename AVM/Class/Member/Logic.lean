
import Prelude
import AVM.Class.Member

namespace AVM.Class

/-- Checks that the number of objects and resources match, and that the
    resources' private data and labels match the objects' private data and
    labels. This check is used in the constructor and method logics. -/
def Member.Logic.checkResourceData (objects : List SomeObject) (resources : List Anoma.Resource) : Bool :=
  objects.length == resources.length
    && List.and (List.zipWith resourceDataEq objects resources)
  where
    resourceDataEq (sobj : SomeObject) (res : Anoma.Resource) : Bool :=
      -- NOTE: We should check the whole resource kind (label + logic) instead
      -- of checking just the label. We should also check that the intent logic
      -- hashes of `sobj.object` and `res` match.
      sobj.label === res.label &&
      sobj.object.quantity == res.quantity &&
        match tryCast sobj.object.privateFields with
        | some privateFields => res.value == privateFields
        | none => false
