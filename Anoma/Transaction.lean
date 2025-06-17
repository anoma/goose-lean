
import Anoma.Resource
import Std.Data.HashMap

namespace Anoma

abbrev Commitment := String
abbrev Nullifier := String

inductive Tag where
  | Created : Commitment → Tag
  | Consumed : Nullifier → Tag
  deriving Inhabited, Repr, BEq, Hashable

abbrev DeltaProof := String
abbrev CommitmentRoot := String

structure Action where
  Data : Type
  -- consumed should be a list of RootedNullifiableResource
  consumed : List Resource
  created : List Resource
  appData : Std.HashMap Tag Data

structure Transaction where
  roots : List CommitmentRoot
  actions : List Action
  deltaProof : DeltaProof

end Anoma
