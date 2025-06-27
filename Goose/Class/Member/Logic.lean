
import Goose.Class.Member

namespace Goose

abbrev Class.Member.Logic (pub : Public) (Args : Type u) := Anoma.Logic.Args (Class.Member.AppData pub Args) → Bool

abbrev Class.Member.SomeLogic (Args : Type u) := Σ (pub : Public), Logic pub Args

def Class.Member.Logic.toSomeLogic {pub : Public} {Args : Type u}
  (log : Class.Member.Logic (pub : Public) (Args : Type u))
  : Class.Member.SomeLogic (Args : Type u)
  := ⟨pub, log⟩

def trueLogic {Args : Type u} {pub : Public} : Class.Member.Logic pub Args :=
  fun _ => True

def falseLogic {Args : Type u} {pub : Public} : Class.Member.Logic pub Args :=
  fun _ => False

/-- Checks that the number of objects and resources match, and that the
      resources' private data and labels match the objects' private data and
      labels. This check is used in the constructor and method logics. -/
def Class.Member.Logic.checkResourceData (objects : List SomeObject) (resources : List Anoma.Resource) : Bool :=
  objects.length == resources.length
    && List.and (List.zipWith resourceDataEq objects resources)
  where
    resourceDataEq (sobj : SomeObject) (res : Anoma.Resource) : Bool :=
      let ⟨sig, obj⟩ := sobj
      @Anoma.rawEq _ _ res.rawVal sig.priv.rawPrivateFields res.value obj.privateFields
        && res.label == sig.classLabel

end Goose
