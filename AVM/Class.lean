import AVM.Class.Member
import AVM.Ecosystem.Label
import AVM.Ecosystem.Member
import AVM.Ecosystem.AppData
import AVM.Intent

namespace AVM

/-- Syntax-level object description (fields + constructors + methods) should
    desugar to the `Class` structure. -/
structure Class {lab : Ecosystem.Label} (classId : lab.ClassId) : Type (u + 1) where
  /-- The constructors of the class. -/
  constructors : (c : classId.label.ConstructorId) → Class.Constructor c
  /-- The destructors of the class. -/
  destructors : (d : classId.label.DestructorId) → Class.Destructor d
  /-- The methods of the class. -/
  methods : (m : classId.label.MethodId) → Class.Method m
  /-- The intents allowed by the class. The intents are not uniquely associated
      with a class. In contrast to constructors, destructors and methods, an
      intent can be a member of multiple different classes. -/
  intents : (l : Intent.Label) → l ∈ classId.label.intentLabels → Intent l
  /-- Extra class-specific logic. The whole resource logic function for an
    object consists of the class invariant and the member logics. -/
  invariant : (self : Object classId.label) → Logic.Args lab → Bool := fun _ _ => true
