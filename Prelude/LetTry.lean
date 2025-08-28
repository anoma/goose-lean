syntax withPosition("let" "try" term (":" term)? ":=" term) optSemicolon(term) : term
syntax withPosition("let" "try" term (":" term)? ":=" term) optSemicolon(doSeq) : doElem
syntax withPosition("let" "try" term (":" term)? "←" term)  optSemicolon(doSeq) : doElem
syntax withPosition("let" "try" term (":" term)? ":=" term) withPosition("failwith" term) optSemicolon(term) : term
syntax withPosition("let" "try" term (":" term)? ":=" term) withPosition("failwith" doSeq) optSemicolon(doSeq) : doElem
syntax withPosition("let" "try" term (":" term)? "←" term) withPosition("failwith" doSeq) optSemicolon(doSeq) : doElem

/-- The `let try x := ov; b` macro unwraps an `Option`, for `ov = some v` binds
  the value `v` to `x` in `b`, for `ov = none` returns `default`. The value
  returned on failure (when `ov = none`) can be specified with the `failwith`
  clause: `let try x := ov failwith failure; b`. The monadic version
  `let try x ← mov; b` can be used when `mov : m (Option V)` for some monad `m`.
  The type of `x` can be specified and `x` can be an arbitrary match pattern. -/
macro_rules
| `(let try $x:term := $e:term ; $body) =>
  `(match ($e) with | none => default | some $x => $body)
| `(let try $x:term : $t:term := $e:term ; $body) =>
  `(match ($e) with | none => default | some ($x : $t) => $body)
| `(let try $x:term := $e:term failwith $r:term ; $body) =>
  `(match ($e) with | none => $r | some $x => $body)
| `(let try $x:term : $t:term := $e:term failwith $r:term ; $body) =>
  `(match ($e) with | none => $r | some ($x : $t) => $body)
| `(doElem| let try $x:term := $e:term ; $body) =>
  `(doElem| match ($e) with | none => default | some $x => $body)
| `(doElem| let try $x:term : $t:term := $e:term ; $body) =>
  `(doElem| match ($e) with | none => default | some ($x : $t) => $body)
| `(doElem| let try $x:term := $e:term failwith $r:doSeq ; $body) =>
  `(doElem| match ($e) with | none => $r | some $x => $body)
| `(doElem| let try $x:term : $t:term := $e:term failwith $r:doSeq ; $body) =>
  `(doElem| match ($e) with | none => $r | some ($x : $t) => $body)
| `(doElem| let try $x:term ← $e:term ; $body) =>
  `(doElem| match ← $e with | none => default | some $x => $body)
| `(doElem| let try $x:term : $t:term ← $e:term ; $body) =>
  `(doElem| match ← $e with | none => default | some ($x : $t) => $body)
| `(doElem| let try $x:term ← $e:term failwith $r:doSeq ; $body) =>
  `(doElem| match ← $e with | none => $r | some $x => $body)
| `(doElem| let try $x:term : $t:term ← $e:term failwith $r:doSeq ; $body) =>
  `(doElem| match ← $e with | none => $r | some ($x : $t) => $body)

/-
#eval let try x := some 42; some (x + 1)
#eval let try y := some 10
      some (y * 3)
#eval let try x := some 1; some (x + 1)
#eval let try x := none; some (x + 1)
#eval let try _ : Nat := none; true
#eval let try (_, y) := some (1, 2); some (y + 1)
-/
