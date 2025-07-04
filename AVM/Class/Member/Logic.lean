
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
      let _ := res.beqVal
      let _ := res.repVal
      let _ := sobj.lab.priv.repPrivateFields
      let _ := res.repLabel
      let _ := res.beqLabel
      sobj.object.quantity == res.quantity &&
      beqCast sobj.lab res.label &&
        match tryCast sobj.object.privateFields with
        | some privateFields => res.value == privateFields
        | none => false
