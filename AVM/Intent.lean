
import Anoma
import Goose.Class

namespace Goose

/-- An Intent is parameterised by arguments and provided objects. It includes an
    intent condition which checks if the desired objects were received. Intents
    are compiled to resources with the conditions compiled to resource logics.
    Intent creation is compiled to transaction submission. -/
structure Intent where
  /-- The type of intent arguments. -/
  Args : Type
  [rawArgs : Anoma.Raw Args]
  /-- The unique label of the intent. -/
  label : String
  /-- The intent condition checks if the desired objects were received. Given
      intent arguments and provided objects, the intent condition is compiled to
      the resource logic of the resource intent. -/
  condition : Args → (provided : List Object) → (received : List Object) → Bool

structure Intent.ResourceData where
  Args : Type
  [rawArgs : Anoma.Raw Args]
  args : Args
  provided : List Object

instance Intent.ResourceData.RawInstance : Anoma.Raw Intent.ResourceData where
  -- NOTE: this should also include a raw representation of the provided objects
  raw appData := appData.rawArgs.raw appData.args

def Intent.toResource (intent : Intent) (args : intent.Args) (provided : List Object) (nonce := 0) (nullifierKeyCommitment := "") : Anoma.Resource :=
  { Val := Intent.ResourceData,
    label := intent.label,
    quantity := 1,
    value := { Args := intent.Args, rawArgs := intent.rawArgs, args, provided },
    ephemeral := false,
    nonce,
    nullifierKeyCommitment }

axiom decidableEqResourceData (A : Type 1) : Decidable (A = Intent.ResourceData)

noncomputable def Intent.ResourceData.fromResource (res : Anoma.Resource) : Option Intent.ResourceData :=
  match decidableEqResourceData res.Val with
  | isTrue h =>
    some (cast h res.value)
  | isFalse _ =>
    none

end Goose
