
import Prelude.UUnit

/-- A monad for boolean checks that supports early return --/
abbrev BoolCheck (ret : Type u := UUnit.{u}) : Type u := Except Bool ret

namespace BoolCheck

def run (b : BoolCheck UUnit) : Bool := match b with
  | (.ok _) => true
  | (.error r) => r

def someOr {A} (m : Option A) (els : Bool) : BoolCheck A := match m with
  | none => .error els
  | (some x) => .ok x

def some {A} (m : Option A) : BoolCheck A := someOr m false

def ret (r : Bool) : BoolCheck UUnit := Except.error r

def guard (b : Bool) : BoolCheck UUnit := if b then pure default else ret false

def fail : BoolCheck UUnit := ret false

end BoolCheck
