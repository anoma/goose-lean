import Anoma
import AVM.Class.Member

namespace AVM

abbrev Logic.Args.{u, v} := Anoma.Logic.Args.{u, v}

/-- Syntax-level object description (fields + constructors + methods) should
    desugar to the `Class` structure. -/
structure Class {lab : Ecosystem.Label} (classId : lab.ClassId) : Type (u + 1) where
  /-- The constructors of the class. -/
  constructors : (c : classId.label.ConstructorId) → Class.Constructor classId c
  /-- The destructors of the class. -/
  destructors : (d : classId.label.DestructorId) → Class.Destructor classId d
  /-- The methods of the class. -/
  methods : (m : classId.label.MethodId) → Class.Method classId m
  /-- Extra class-specific logic for the resource logic of the object resource. -/
  invariant : (self : Object classId) → Logic.Args → Bool := fun _ _ => true
