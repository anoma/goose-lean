
import Anoma.Action

namespace Anoma

abbrev DeltaProof := String

structure Transaction where
  actions : List Action
  deltaProof : DeltaProof
