
import Anoma.Resource
import Std.Data.HashMap

namespace Anoma

abbrev Commitment := String
abbrev Nullifier := String

inductive Tag where
  | Created : Commitment → Tag
  | Consumed : Nullifier → Tag
  deriving Inhabited, Repr, BEq, Hashable

abbrev RawTag := String

def Tag.toRaw (tag : Tag) : RawTag := match tag with
 | (Created m) => m
 | (Consumed m) => m

def Tag.fromResource (isConsumed : Bool) (res : Resource) : Tag :=
  if isConsumed then
    Tag.Consumed res.nullifier
  else
    Tag.Created res.commitment

def RawTag.fromResource (isConsumed : Bool) (res : Resource) : RawTag :=
  Tag.toRaw (Tag.fromResource isConsumed res)

abbrev DeltaProof := String

structure Action where
  Data : Type
  [rawData : Raw Data]
  consumed : List RootedNullifiableResource
  created : List Resource
  -- TODO clarify wether the key should be RawTag or Tag
  appData : Std.HashMap RawTag Data

structure Transaction where
  roots : List CommitmentRoot
  actions : List Action
  deltaProof : DeltaProof

end Anoma
