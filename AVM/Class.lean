
import AVM.Class.AppData
import AVM.Intent

namespace AVM

/-- Syntax-level object description (fields + constructors + methods) should
    desugar to the `Class` structure. -/
structure Class (lab : Class.Label) where
  /-- The constructors of the class. -/
  constructors : (c : lab.ConstructorId) -> Class.Constructor c
  /-- The methods of the class. -/
  methods : (m : lab.MethodId) -> Class.Method m
  /-- The intents known by and allowed for the class. The intents are not
    uniquely associated with a class. In contrast to constructors and methods,
    an intent can be a member of multiple different classes. -/
  intents : lab.IntentId -> Intent
  /-- Extra class-specific logic. The whole resource logic function for an
    object consists of the class invariant and the member logics. -/
  invariant : (self : Object lab) → Class.Logic.Args lab → Bool := fun _ _ => true
