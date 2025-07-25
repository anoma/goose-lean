
import Prelude

namespace AVM

structure Intent.Label where
  /-- The type of intent arguments. The arguments are stored in the `label`
    field of the intent resource (see `Intent.ResourceData` in
    `AVM/Intent.lean`). The intent arguments are not provided in the
    app data for any resource logics. -/
  Args : SomeType
  /-- The unique name of the intent. -/
  name : String
  deriving BEq

instance Intent.Label.hasTypeRep : TypeRep Intent.Label where
  rep := Rep.atomic "AVM.Intent.Label"

instance Intent.Label.hasHashable : Hashable Intent.Label where
  hash a := hash a.name
