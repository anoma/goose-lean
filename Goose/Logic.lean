
import Goose.Object
import Anoma.Resource

namespace Goose

abbrev Action.Logic (Args : Type u) := Anoma.Logic.Args (Object.AppData Args) → Bool

def trueLogic {Args : Type u} : Action.Logic Args :=
  fun _ => True

def falseLogic {Args : Type u} : Action.Logic Args :=
  fun _ => False

end Goose
