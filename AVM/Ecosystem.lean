import AVM.Ecosystem.Label
import AVM.Ecosystem.Member
import AVM.Class

namespace AVM

structure Ecosystem (label : Ecosystem.Label) : Type (u + 1) where
  classes : (c : label.ClassId) → Class c
  functions : (f : label.FunctionId) → Function f
