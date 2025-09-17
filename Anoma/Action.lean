
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

structure LogicVerifierInput : Type 1 where
  status : ConsumedCreated
  Data : SomeType.{0}
  appData : Data.type
  logicVKOuter : LogicVKOuterHash := ""
  proof: String := ""

structure Action : Type 1 where
  complianceUnits : List ComplianceUnit
  logicVerifierInputs : Std.HashMap Tag LogicVerifierInput
