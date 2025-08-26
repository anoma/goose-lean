import AVM.Class.Member

namespace AVM

abbrev Logic.Args := Anoma.Logic.Args Unit

/-- Syntax-level object description (fields + constructors + methods) should
    desugar to the `Class` structure. -/
structure Class (label : Class.Label) : Type (u + 1) where
  /-- The constructors of the class. -/
  constructors : (c : label.ConstructorId) → Class.Constructor c
  /-- The destructors of the class. -/
  destructors : (d : label.DestructorId) → Class.Destructor d
  /-- The methods of the class. -/
  methods : (m : label.MethodId) → Class.Method m
  /-- Extra class-specific logic. The whole resource logic function for an
    object consists of the class invariant and the member logics. -/
  invariant : (self : Object label) → Logic.Args → Bool := fun _ _ => true
