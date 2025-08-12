
import Prelude
import Anoma.Compliance

namespace Anoma

abbrev DeltaProof := String

structure DeltaWitness : Type 1 where
  signingKey : String

def DeltaWitness.fromComplianceWitnesses (witnesses : List ComplianceWitness) : DeltaWitness :=
  { signingKey := witnesses.map ComplianceWitness.rcv |>.foldl (· ++ ·) "" }
