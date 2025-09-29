import AVM.Ecosystem.Label

import Lean
open Lean

namespace AVM.Scope

structure Label where
  EcosystemId : Type
  EcosystemIdEnum : FinEnum EcosystemId
  ecosystem : EcosystemId → Ecosystem.Label

namespace Label

-- TODO rename/remove
abbrev fin (s : Label) : Fin s.EcosystemIdEnum.card → s.EcosystemId := s.EcosystemIdEnum.equiv.invFun

abbrev EcosystemId.label {lab : Label} (e : lab.EcosystemId) : Ecosystem.Label :=
  lab.ecosystem e

structure InScope (l : Ecosystem.Label) (lab : Scope.Label) where
  eid : lab.EcosystemId
  proof : eid.label = l := by rfl

notation l " ∈ " lab:50 => InScope l lab

end Scope.Label

abbrev Ecosystem.Label.toScope (lab : Ecosystem.Label) : Scope.Label where
  EcosystemId := Unit
  EcosystemIdEnum := {
    card := 1
    equiv := {
      toFun := fun _ => 0
      invFun := fun _ => .unit
      right_inv := by grind}}
  ecosystem := fun .unit => lab
