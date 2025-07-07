
import Anoma
import AVM.Class

namespace AVM

/-- An Intent is parameterised by arguments and provided objects. It includes an
    intent condition which checks if the desired objects were received. Intents
    are compiled to resources with the conditions compiled to resource logics.
    Intent creation is compiled to transaction submission. -/
structure Intent where
  /-- The type of intent arguments. -/
  Args : SomeType
  /-- The unique label of the intent. -/
  label : String
  /-- The intent condition checks if the desired objects were received. Given
      intent arguments and provided objects, the intent condition is compiled to
      the resource logic of the resource intent. -/
  condition : Args.type → (provided : List SomeObject) → (received : List SomeObject) → Bool

structure Intent.ResourceData where
  Args : SomeType
  args : Args.type
  provided : List SomeObject

instance Intent.ResourceData.hasTypeRep : TypeRep ResourceData where
  rep := Rep.atomic "AVM.Intent.ResourceData"

instance Intent.ResourceData.hasBEq : BEq Intent.ResourceData where
  beq a b :=
    a.args === b.args && a.provided == b.provided

def Intent.toResource (intent : Intent) (args : intent.Args.type) (provided : List SomeObject) (nonce := 0) (nullifierKeyCommitment : Anoma.NullifierKeyCommitment := default) : Anoma.Resource :=
  { Val := ⟨Intent.ResourceData⟩,
    Label := ⟨String⟩,
    label := intent.label,
    quantity := 1,
    value := {
      Args := intent.Args,
      args,
      provided
    },
    ephemeral := false,
    nonce,
    nullifierKeyCommitment }

def Intent.ResourceData.fromResource (res : Anoma.Resource) : Option Intent.ResourceData :=
  tryCast res.value
