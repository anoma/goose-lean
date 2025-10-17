import AVM.Scope.Label
import AVM.Ecosystem
import AVM.Class.Translation.Logics

namespace AVM

structure Scope (lab : Scope.Label) where
  ecosystems (eid : lab.EcosystemId) : Ecosystem eid.label

abbrev Ecosystem.toScope {lab : Ecosystem.Label} (eco : Ecosystem lab) : Scope lab.toScope where
  ecosystems := fun .unit => eco

def Scope.logics {lab : Scope.Label} (s : Scope lab) : List Anoma.Logic :=
  lab.EcosystemIdEnum.toList.flatMap fun e =>
   let eco := s.ecosystems e
   e.label.classesEnum.toList.flatMap fun c =>
     let cl := eco.classes c
     c.label.constructorsEnum.toList.map fun m =>
       let ctr := cl.constructors m
       Class.Constructor.Message.logic ctr
