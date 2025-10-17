
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

instance NullifierKeyCommitment.hasTypeRep : TypeRep NullifierKeyCommitment where
  rep := Rep.atomic "NullifierKeyCommitment"

/-- A proof that a NullifierKey matches a NullifierKeyCommitment -/
inductive NullifierKeyMatchesCommitment : (key : NullifierKey) → (nfc : NullifierKeyCommitment) → Prop where
  | universal : NullifierKeyMatchesCommitment .universal .universal
  | secret : {n m : Nat} → n = m → NullifierKeyMatchesCommitment (.secret n) (.ofSecret m)

def checkNullifierKey (key : NullifierKey) (nfc : NullifierKeyCommitment) : Decidable (NullifierKeyMatchesCommitment key nfc) :=
  match key, nfc with
   | .universal, .universal => isTrue .universal
   | .secret n, .ofSecret m => match decEq n m with
     | isTrue p => isTrue (.secret p)
     | isFalse np => isFalse (fun h => match h with | .secret p' => np p')
   | .universal, .ofSecret _ => isFalse (fun h => nomatch h)
   | .secret _, .universal => isFalse (fun h => nomatch h)

/-- Computes the commitment of a NullifierKey -/
def NullifierKey.commitment (k : NullifierKey) : NullifierKeyCommitment :=
  match k with
  | .universal => .universal
  | .secret s => .ofSecret s
