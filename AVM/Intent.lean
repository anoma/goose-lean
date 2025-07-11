
import Anoma
import AVM.Object

namespace AVM

/-- An Intent is parameterised by arguments and provided objects. It includes an
    intent condition which checks if the desired objects were received. Intents
    are compiled to resources with the conditions compiled to resource logics.
    Intent creation is compiled to transaction submission. -/
structure Intent where
  /-- The type of intent arguments. The arguments are stored in the `value`
    field of the intent resource. They are not provided in the app data for any
    resource logics. -/
  Args : SomeType
  /-- The unique label of the intent. The textual representation (via Repr) of
    the IntentId constructor corresponding to an intent must be equal to the
    intent's label. -/
  label : String
  /-- The intent condition checks if the desired objects were received. Given
      intent arguments and provided objects, the intent condition is compiled to
      the resource logic of the resource intent. -/
  condition : Args.type → (provided : List SomeObject) → (received : List SomeObject) → Bool

/-- Intent.ResourceData is stored in the `value` field of the intent resource. -/
structure Intent.ResourceData.{u} where
  Args : SomeType.{u}
  args : Args.type
  provided : List SomeConsumedObject.{u}

instance Intent.ResourceData.hasTypeRep : TypeRep ResourceData where
  rep := Rep.atomic "AVM.Intent.ResourceData"

instance Intent.ResourceData.hasBEq : BEq Intent.ResourceData where
  beq a b :=
    a.args === b.args && a.provided == b.provided

def Intent.toResource (intent : Intent) (args : intent.Args.type) (provided : List SomeConsumedObject) (nonce := 0) (nullifierKeyCommitment : Anoma.NullifierKeyCommitment := default) : Anoma.Resource :=
  { Val := ⟨Intent.ResourceData⟩,
    Label := ⟨String⟩,
    label := intent.label,
    quantity := 1,
    value := {
      Args := intent.Args,
      args,
      provided
    },
    ephemeral := true,
    nonce,
    nullifierKeyCommitment }

def Intent.ResourceData.fromResource (res : Anoma.Resource.{u,v}) : Option Intent.ResourceData.{u} :=
  tryCast res.value
