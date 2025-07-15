
import Prelude
import Anoma.Compliance

namespace Anoma

inductive Tag where
  | Created : Commitment → Tag
  | Consumed : Nullifier → Tag
  deriving Inhabited, Repr, BEq, Hashable

abbrev LogicVKOuterHash := String

inductive DeletionCriterion where
  | DeleteImmediately
  | StoreForever

structure LogicVerifierInput where
  Data : SomeType
  status : ConsumedCreated
  logicVKOuter : LogicVKOuterHash
  applicationData : List (Data.type × DeletionCriterion)
  proof: String

structure Action where
  complianceUnits : List ComplianceUnit
  logicVerifierInputs : Std.HashMap Tag LogicVerifierInput
