
import Goose.Class.Member

namespace Goose

abbrev Class.Member.Logic (Args : Type) := Anoma.Logic.Args (Class.Member.AppData Args) → Bool

def trueLogic {Args : Type} : Class.Member.Logic Args :=
  fun _ => True

def falseLogic {Args : Type} : Class.Member.Logic Args :=
  fun _ => False

/-- Checks that the number of objects and resources match, and that the
      resources' private data and labels match the objects' private data and
      labels. This check is used in the constructor and method logics. -/
def Class.Member.Logic.checkResourceData (objects : List Object) (resources : List Anoma.Resource) : Bool :=
  objects.length == resources.length
    && List.and (List.zipWith resourceDataEq objects resources)
  where
    resourceDataEq (obj : Object) (res : Anoma.Resource) : Bool :=
      @Anoma.rawEq _ _ res.rawVal obj.rawPrivateFields res.value obj.privateFields
        && res.label == obj.classLabel

end Goose
