import AVM.Scope.Label
import AVM.Ecosystem
import AVM.Class.Translation.Logics

namespace AVM

structure Scope (lab : Scope.Label) where
  ecosystems (eid : lab.EcosystemId) : Ecosystem eid.label

abbrev Ecosystem.toScope {lab : Ecosystem.Label} (eco : Ecosystem lab) : Scope lab.toScope where
  ecosystems := fun .unit => eco

def Scope.logics {lab : Scope.Label} (s : Scope lab) : List Anoma.Logic :=
  Logic.builtinLogics ++
  lab.EcosystemIdEnum.toList.flatMap fun e =>
   let eco := s.ecosystems e
   e.label.classesEnum.toList.map fun c =>
     Class.logic eco c
