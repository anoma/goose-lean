
import Prelude
import Anoma.Resource

namespace Anoma

abbrev MerklePath := List Nat

structure ComplianceWitness : Type 2 where
    consumedResource : Resource
    createdResource : Resource
    /-- Nullifier key of the consumed resource -/
    nfKey : NullifierKey
    /-- Random scalar for delta commitment -/
    rcv : String
    /-- The path from the consumed commitment to the root in the commitment tree -/
    merklePath : MerklePath := []
    /-- The existing root for the ephemeral resource -/
    ephemeralRoot : String := ""

structure ComplianceInstance where

abbrev ComplianceProof := String

structure ComplianceUnit : Type 2 where
  proof : ComplianceProof
  inst : ComplianceInstance

  /-- used only by the evaluator.-/
  witness : ComplianceWitness

def ComplianceUnit.create (witness : ComplianceWitness) : ComplianceUnit :=
  -- This is a placeholder implementation.
  { proof := "", inst := { }, witness }
