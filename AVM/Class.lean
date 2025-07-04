
import AVM.Class.AppData

namespace AVM

/-- Syntax-level object description (fields + constructors + methods) should
    desugar to the `Class` structure. -/
structure Class (lab : Class.Label) where
  constructors : (c : lab.ConstructorId) -> Class.Constructor c
  methods : (m : lab.MethodId) -> Class.Method m
  /-- Extra class-specific logic. The whole resource logic function for an
     object consists of the class invariant and the method and constructor logics.
     -/
  invariant : (self : Object lab) → Anoma.Logic.Args (Class.AppData lab) → Bool
