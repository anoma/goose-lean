
import Anoma
import Goose.Class

namespace Goose

/-- An Intent is parameterised by arguments and provided objects. It includes an
    intent condition which checks if the desired objects were received. Intent
    are compiled to resources with the conditions compiled to resource logics.
    Intent creation is compiled to transaction submission. -/
structure Intent where
  /-- The type of intent arguments. -/
  Args : Type
  [rawArgs : Anoma.Raw Args]
  /-- The unique label of the intent. -/
  label : String
  /-- The intent condition checks if the desired objects were received. Given
      intent arguments and provided objects, the intent condition is compiled to
      the resource logic of the resource intent. -/
  condition : Args → (provided : List Object) → (received : List Object) → Bool

end Goose
