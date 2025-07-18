import AVM.Ecosystem.Label
import AVM.Ecosystem.Member
import AVM.Class

namespace AVM

structure Ecosystem (label : EcosystemLabel) : Type (u + 1) where
  classes : (c : label.ClassId) → Class c
  functions : (f : label.FunctionId) → Function f
  /-- The intents known by and allowed for the Ecosystem. The intents are not
    uniquely associated with an ecosystem. In contrast to functions,
    an intent can be a member of multiple different ecosystems. -/
  intents : label.IntentId → Intent
