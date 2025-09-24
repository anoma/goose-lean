import Mathlib.Data.Fintype.Basic
import Prelude

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
def checkKey (pub : PublicKey) (priv : PrivateKey) : Bool := pub.key == priv.key

structure Signature {A : Type u} (msg : A) : Type u where
  msg : A
  signature : PrivateKey

-- Mock function that returns the `raw` bytes of the signature
def Signature.raw {A : Type u} (msg : A) (_s : Signature msg ) : Nat := 0

instance {A B} (msgA : A) (msgB : B) : HBEq (Signature msgA) (Signature msgB) where
  hbeq a b := a.raw == b.raw

def Signature.sign {A : Type u} (msg : A) (key : PrivateKey) : Signature msg where
  signature := key
  msg

-- mock function
def checkSignature {A : Type u} {msg : A} (sig : Signature msg) (pub : PublicKey) : Bool := checkKey pub sig.signature
