
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
  [repArgs : TypeRep Args]
  [beqArgs : BEq Args]
  /-- The unique label of the intent. -/
  label : String
  /-- The intent condition checks if the desired objects were received. Given
      intent arguments and provided objects, the intent condition is compiled to
      the resource logic of the resource intent. -/
  condition : Args → (provided : List SomeObject) → (received : List SomeObject) → Bool

structure Intent.ResourceData where
  Args : Type
  [repArgs : TypeRep Args]
  [beqArgs : BEq Args]
  args : Args
  provided : List SomeObject

instance Intent.ResourceData.hasTypeRep : TypeRep Intent.ResourceData where
  rep := Rep.atomic "Intent.ResourceData"

instance Intent.ResourceData.hasBEq : BEq Intent.ResourceData where
  beq a b :=
    let _ : TypeRep a.Args := a.repArgs
    let _ : TypeRep b.Args := b.repArgs
    let _ : BEq b.Args := b.beqArgs
    beqCast a.args b.args && a.provided == b.provided

def Intent.toResource (intent : Intent) (args : intent.Args) (provided : List SomeObject) (nonce := 0) (nullifierKeyCommitment := "") : Anoma.Resource :=
  { Val := Intent.ResourceData,
    label := intent.label,
    quantity := 1,
    value := {
      Args := intent.Args,
      repArgs := intent.repArgs,
      beqArgs := intent.beqArgs,
      args,
      provided
    },
    ephemeral := false,
    nonce,
    nullifierKeyCommitment }

def Intent.ResourceData.fromResource (res : Anoma.Resource) : Option Intent.ResourceData :=
  let _ : TypeRep res.Val := res.repVal
  tryCast res.value

end Goose
