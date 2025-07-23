
import Anoma
import AVM.Object
import AVM.Intent.Label

namespace AVM

/-- An Intent is parameterised by arguments and provided objects. It includes an
    intent condition which checks if the desired objects were received. Intents
    are compiled to resources with the conditions compiled to resource logics.
    Intent creation is compiled to transaction submission. -/
structure Intent (ilab : Intent.Label) where
  /-- The intent condition checks if the desired objects were received. Given
      intent arguments and provided objects, the intent condition is compiled to
      the resource logic of the resource intent. -/
  condition : ilab.Args.type → (provided : List SomeObject) → (received : List SomeObject) → Bool

/-- Intent.ResourceData is stored in the `label` field of the intent resource. -/
structure Intent.ResourceData.{u} where
  Args : SomeType.{u}
  args : Args.type
  provided : List SomeObject.{u}

instance Intent.ResourceData.hasTypeRep : TypeRep ResourceData where
  rep := Rep.atomic "AVM.Intent.ResourceData"

instance Intent.ResourceData.hasBEq : BEq Intent.ResourceData where
  beq a b :=
    a.args === b.args && a.provided == b.provided

structure Intent.LabelData : Type (u + 1) where
  /-- The unique label of the intent. -/
  label : Intent.Label.{u}
  data : Intent.ResourceData.{u}
  deriving BEq

instance Intent.LabelData.hasTypeRep : TypeRep Intent.LabelData where
  rep := Rep.atomic "AVM.Intent.LabelData"

def Intent.toResource {ilab : Intent.Label} (_intent : Intent ilab) (args : ilab.Args.type) (provided : List SomeObject) (nonce : Anoma.Nonce) (nullifierKeyCommitment : Anoma.NullifierKeyCommitment := default) : Anoma.Resource :=
  { Val := ⟨Unit⟩,
    Label := ⟨Intent.LabelData⟩,
    label := {
      label := ilab,
      data := {
        Args := ⟨ilab.Args⟩,
        args,
        provided
      }
    },
    quantity := 1,
    value := (),
    ephemeral := true,
    nonce,
    nullifierKeyCommitment }

def Intent.LabelData.fromResource (res : Anoma.Resource.{u,v}) : Option Intent.LabelData.{u} :=
  tryCast res.label

def Intent.ResourceData.fromResource (res : Anoma.Resource.{u,v}) : Option Intent.ResourceData.{u} := do
  let labelData : Intent.LabelData.{u} ← Intent.LabelData.fromResource res
  some labelData.data
