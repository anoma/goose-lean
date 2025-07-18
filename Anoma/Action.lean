
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

structure LogicVerifierInput : Type (u + 1) where
  Data : SomeType.{u}
  status : ConsumedCreated
  appData : Data.type
  logicVKOuter : LogicVKOuterHash := ""
  proof: String := ""

structure Action : Type (u + 1) where
  complianceUnits : List ComplianceUnit
  logicVerifierInputs : Std.HashMap Tag LogicVerifierInput.{u}
