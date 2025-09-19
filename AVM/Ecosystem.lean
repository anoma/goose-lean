import AVM.Class
import AVM.Ecosystem.Label
import AVM.Ecosystem.Member

namespace AVM

/-- Ecosystem is a collection of classes. -/
structure Ecosystem (label : Ecosystem.Label) : Type 1 where
  classes : (c : label.ClassId) → Class c
  multiMethods : (f : label.MultiMethodId) → Ecosystem.MultiMethod f
