
import Prelude
import Anoma.Resource

namespace Anoma

abbrev MerklePath := List Nat

structure ComplianceWitness.{u, v} : Type (max u v + 1) where
    consumedResource : Resource.{u, v}
    createdResource : Resource.{u, v}
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

structure ComplianceUnit.{u, v} : Type (max u v + 1) where
  proof : ComplianceProof
  inst : ComplianceInstance

  /-- used only by the evaluator.-/
  witness : ComplianceWitness.{u, v}

def ComplianceUnit.create (witness : ComplianceWitness.{u, v}) : ComplianceUnit.{u, v} :=
  -- This is a placeholder implementation.
  { proof := "", inst := { }, witness }
