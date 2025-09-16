
import Prelude
import Anoma.NullifierKey

namespace Anoma

structure Nonce where
 value : Nat
 deriving BEq

instance Nonce.hasTypeRep : TypeRep Nonce where
  rep := Rep.atomic "Nonce"

instance Nonce.instInhabited : Inhabited Nonce where
  default := ⟨0⟩

def Nonce.todo : Nonce where
  value := 0
