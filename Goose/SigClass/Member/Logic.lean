
import Goose.SigClass.Member

namespace SigGoose

abbrev Class.Member.Logic (pub : Public) (Args : Type u) := Anoma.Logic.Args (Class.Member.AppData pub Args) → Bool

def trueLogic {Args : Type u} {pub : Public} : Class.Member.Logic pub Args :=
  fun _ => True

def falseLogic {Args : Type u} {pub : Public} : Class.Member.Logic pub Args :=
  fun _ => False

/-- Checks that the number of objects and resources match, and that the
      resources' private data and labels match the objects' private data and
      labels. This check is used in the constructor and method logics. -/
def Class.Member.Logic.checkResourceData {sig : Signature} (objects : List (Object sig)) (resources : List Anoma.Resource) : Bool :=
  objects.length == resources.length
    && List.and (List.zipWith resourceDataEq objects resources)
  where
    resourceDataEq (obj : Object sig) (res : Anoma.Resource) : Bool :=
      @Anoma.rawEq _ _ res.rawVal (Private.rawPrivateFields sig.priv) res.value obj.privateFields
        && res.label == sig.classLabel

end SigGoose
