
import Prelude
import Anoma.Compliance

namespace Anoma

abbrev DeltaProof := String

structure DeltaWitness : Type 1 where
  signingKey : String

def DeltaWitness.fromComplianceWitnesses (witnesses : List ComplianceWitness) : DeltaWitness :=
  { signingKey := witnesses.map ComplianceWitness.rcv |>.foldl (· ++ ·) "" }

def DeltaWitness.compose (witness1 witness2 : DeltaWitness) : DeltaWitness :=
  { signingKey := witness1.signingKey ++ witness2.signingKey }
