import AVM.Ecosystem.Label

namespace AVM.Scope

structure Label where
  EcosystemId : Type
  ecosystem : EcosystemId → Ecosystem.Label

namespace Label

abbrev EcosystemId.label {lab : Label} (e : lab.EcosystemId) : Ecosystem.Label :=
  lab.ecosystem e

structure InScope (l : Ecosystem.Label) (lab : Scope.Label) where
  eid : lab.EcosystemId
  proof : eid.label = l := by rfl

notation l " ∈ " lab:50 => InScope l lab

end Scope.Label

abbrev Ecosystem.Label.toScope (lab : Ecosystem.Label) : Scope.Label where
  EcosystemId := Unit
  ecosystem := fun .unit => lab
