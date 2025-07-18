
import AVM.Class.Member
import AVM.Ecosystem.Label
import AVM.Ecosystem.Member
import AVM.Ecosystem.AppData
import AVM.Intent

namespace AVM

/-- Syntax-level object description (fields + constructors + methods) should
    desugar to the `Class` structure. -/
structure Class {lab : EcosystemLabel} (classId : lab.ClassId) : Type (u + 1) where
  /-- The constructors of the class. -/
  constructors : (c : classId.label.ConstructorId) → Class.Constructor c
  /-- The methods of the class. -/
  methods : (m : classId.label.MethodId) → Class.Method m
  /-- The destructors of the class. -/
  destructors : (m : classId.label.DestructorId) → Class.Destructor m
  /-- Extra class-specific logic. The whole resource logic function for an
    object consists of the class invariant and the member logics. -/
  invariant : (self : Object classId.label) → Ecosystem.Logic.Args lab → Bool := fun _ _ => true
