import AVM.Class.Member
import AVM.Intent

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
  /-- The intents allowed by the class. The intents are not uniquely associated
      with a class. In contrast to constructors, destructors and methods, an
      intent can be a member of multiple different classes. -/
  intents : (l : Intent.Label) → l ∈ label.intentLabels → Intent l
  /-- Extra class-specific logic. The whole resource logic function for an
    object consists of the class invariant and the member logics. -/
  invariant : (self : Object label) → Logic.Args → Bool := fun _ _ => true
