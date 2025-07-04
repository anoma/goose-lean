namespace BoolCheck

/-- A monad for boolean checks that supports early return --/
abbrev BoolCheck (ret : Type := Unit) : Type := Except Bool ret

def run (b : BoolCheck Unit) : Bool := match b with
  | (.ok _) => True
  | (.error r) => r

def someOr (m : Option A) (els : Bool) : BoolCheck A := match m with
  | none => .error els
  | (some x) => .ok x

def some (m : Option A) : BoolCheck A := someOr m False

def ret (r : Bool) : BoolCheck Unit := Except.error r

def guard (b : Bool) : BoolCheck Unit := if b then pure Unit.unit else ret False

end BoolCheck

export BoolCheck (BoolCheck)
