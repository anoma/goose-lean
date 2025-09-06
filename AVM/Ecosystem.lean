import AVM.Class
import AVM.Ecosystem.Label
import AVM.Ecosystem.Member

namespace AVM

/-- Ecosystem is a collection of classes. -/
structure Ecosystem (label : Ecosystem.Label) where
  classes : (c : label.ClassId) → Class c
  multimethods : (f : label.MultiMethodId) → MultiMethod f
