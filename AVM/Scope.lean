import AVM.Scope.Label
import AVM.Ecosystem

namespace AVM

structure Scope (lab : Scope.Label) where
  ecosystems (eid : lab.EcosystemId) : Ecosystem eid.label

abbrev Ecosystem.toScope {lab : Ecosystem.Label} (eco : Ecosystem lab) : Scope lab.toScope where
  ecosystems := fun .unit => eco
