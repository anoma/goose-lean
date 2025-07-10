import Prelude

namespace Anoma

/-- A secret value. Used to assign ownership to a Resource -/
inductive NullifierKey where
  /-- Everyone knows this key -/
  | universal : NullifierKey
  | secret : Nat → NullifierKey
  deriving Repr, BEq, Hashable

/-- Commitment to a nullifierkey. Used to prove that you own a NullifierKey without revealing it -/
inductive NullifierKeyCommitment where
  /-- Commitment of the universal NullifierKey -/
  | universal : NullifierKeyCommitment
  /-- The commitment of a secret key. Pattern matching on the argument should
  only be done by internal functions in this file -/
  | ofSecret : (privateNat : Nat) → NullifierKeyCommitment
  deriving Repr, BEq, Hashable, DecidableEq

instance NullifierKeyCommitment.instInhabited : Inhabited NullifierKeyCommitment where
  default := .universal

/-- A proof that a NullifierKey matches a NullifierKeyCommitment -/
inductive NullifierKeyProof : (key : NullifierKey) → (nfc : NullifierKeyCommitment) → Prop where
  | universal : NullifierKeyProof .universal .universal
  | secret : {n m : Nat} → n = m → NullifierKeyProof (.secret n) (.ofSecret m)

def checkNullifierKey (key : NullifierKey) (nfc : NullifierKeyCommitment) : Decidable (NullifierKeyProof key nfc) :=
  match key, nfc with
   | .universal, .universal => isTrue .universal
   | .secret n, .ofSecret m => match decEq n m with
     | isTrue p => isTrue (.secret p)
     | isFalse np => isFalse
        (by
          intro h
          cases h
          contradiction)
   | .universal, .ofSecret m => isFalse
        (by
          intro h
          cases h)
   | .secret n, .universal => isFalse
        (by
          intro h
          cases h)

/-- Computes the commitment of a NullifierKey -/
def NullifierKey.commitment (k : NullifierKey) : NullifierKeyCommitment :=
  match k with
  | .universal => .universal
  | (.secret s) => .ofSecret s

/-- A public value derived from a secret NullifierKey and a Resource -/
inductive Nullifier where
  | privateMk : Nullifier
  deriving Repr, BEq, Hashable

/-- Temporary nullifier that should eventually be replaced with a proper one -/
def Nullifier.todo : Nullifier := privateMk

instance : TypeRep NullifierKeyCommitment where
  rep := Rep.atomic "NullifierKeyCommitment"
