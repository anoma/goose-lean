import Mathlib.Data.Fintype.Basic
import AVM

namespace Applib

structure PublicKey where
  key : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

instance PublicKey.hasTypeRep : TypeRep PublicKey where
  rep := Rep.atomic "PublicKey"

structure PrivateKey where
  key : Nat
  deriving Repr, BEq, Hashable, DecidableEq

-- mock function
def checkKey (pub : PublicKey) (priv : PrivateKey) : Bool := pub.key == priv.key
