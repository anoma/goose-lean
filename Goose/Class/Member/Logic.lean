
import Goose.Class.Member

namespace Goose

abbrev Class.Member.Logic (pub : Public) (Args : Type u) := Anoma.Logic.Args (Class.Member.AppData pub Args) → Bool

structure Class.Member.SomeLogic (Args : Type u) where
  {pub : Public}
  logic : Logic pub Args

def Class.Member.Logic.toSomeLogic {pub : Public} {Args : Type u}
  (logic : Class.Member.Logic (pub : Public) (Args : Type u))
  : Class.Member.SomeLogic (Args : Type u)
  := {logic}

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
      let _ := res.beqVal
      let _ := res.repVal
      let _ := sobj.sig.priv.repPrivateFields
      res.label == sobj.sig.classLabel &&
        match tryCast sobj.object.privateFields with
        | some privateFields => res.value == privateFields
        | none => false

end Goose
