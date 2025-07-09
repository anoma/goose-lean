
import Anoma.Resource
import Std.Data.HashMap

namespace Anoma

inductive Tag where
  | Created : Commitment → Tag
  | Consumed : Nullifier → Tag
  deriving Inhabited, Repr, BEq, Hashable

abbrev DeltaProof := String

structure Action where
  Data : SomeType.{u}
  consumed : List RootedNullifiableResource
  created : List Resource
  /-- `appData` contains public data for each resource in the action -/
  appData : Std.HashMap Tag Data.type

structure Transaction where
  roots : List CommitmentRoot
  actions : List Action
  deltaProof : DeltaProof

end Anoma
