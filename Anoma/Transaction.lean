
import Anoma.Resource
import Std.Data.HashMap

namespace Anoma

abbrev Commitment := String
abbrev Nullifier := String

inductive Tag where
  | Created : Commitment → Tag
  | Consumed : Nullifier → Tag
  deriving Inhabited, Repr, BEq, Hashable

def Tag.fromResource (isConsumed : Bool) (res : Resource) : Tag :=
  if isConsumed then
    Tag.Consumed res.nullifier
  else
    Tag.Created res.commitment

abbrev DeltaProof := String

structure Action where
  Data : Type u
  [repData : TypeRep Data]
  [beqData : BEq Data]
  consumed : List RootedNullifiableResource
  created : List Resource
  /-- `appData` contains public data for each resource in the action -/
  appData : Std.HashMap Tag Data

structure Transaction where
  roots : List CommitmentRoot
  actions : List Action
  deltaProof : DeltaProof

end Anoma
