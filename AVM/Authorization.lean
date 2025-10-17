import Mathlib.Data.Fintype.Basic
import Prelude
import AVM.Message.Data

namespace AVM

structure PublicKey where
  key : Nat
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited

def PublicKey.universal : PublicKey where
  key := 0

instance PublicKey.hasTypeRep : TypeRep PublicKey where
  rep := Rep.atomic "PublicKey"

structure PrivateKey where
  key : Nat
  deriving Repr, BEq, Hashable, DecidableEq

def PrivateKey.universal : PrivateKey where
  key := 0

-- mock function
private def checkKey (pub : PublicKey) (priv : PrivateKey) : Bool := pub.key == priv.key

structure Signature where
  private signature : PrivateKey

-- Mock function that returns the `raw` bytes of the signature
def Signature.raw (_s : Signature) : Nat := 0

instance : BEq Signature where
  beq a b := a.raw == b.raw

def Signature.sign {lab : Ecosystem.Label} (_msg : MessageData lab) (key : PrivateKey) : Signature where
  signature := key

-- mock function
def checkSignature {lab : Ecosystem.Label} (_msg : MessageData lab) (sig : Signature) (pub : PublicKey) : Bool := checkKey pub sig.signature
