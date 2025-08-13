syntax withPosition("let!" term (":" term)? ":=" term) optSemicolon(term) : term
syntax withPosition("let!" term ":=" term) optSemicolon(doSeq) : doElem
syntax withPosition("let!" term ":" term ":=" term) optSemicolon(doSeq) : doElem
syntax withPosition("let!" term (":" term)? "←" term)  optSemicolon(doSeq) : doElem
syntax withPosition("let!" term (":" term)? ":=" term) "failwith" term optSemicolon(term) : term
syntax withPosition("let!" term (":" term)? ":=" term) "failwith" doSeq optSemicolon(doSeq) : doElem
syntax withPosition("let!" term (":" term)? "←" term) "failwith" doSeq optSemicolon(doSeq) : doElem

/-- The `let! pat := v; b` syntax desugars to `match v with | pat => b | _ => default`.
  The value returned on failure (instead of `default`, when `v` does not match `pat`)
  can be specified with the `failwith` clause: `let! pat := v failwith failure; b`.
  The monadic version `let! x ← mv; b` can be used when `mv : m V` for some monad `m`.
  The type of `pat` can be specified. -/
macro_rules
| `(let! $x:term := $e:term ; $body) =>
  `(match ($e) with | $x => $body | _ => default)
| `(let! $x:term : $t:term := $e:term ; $body) =>
  `(match ($e) with | ($x : $t) => $body | _ => default)
| `(let! $x:term := $e:term failwith $r:term ; $body) =>
  `(match ($e) with | $x => $body | _ => $r)
| `(let! $x:term : $t:term := $e:term failwith $r:term ; $body) =>
  `(match ($e) with | ($x : $t) => $body | _ => $r)
| `(doElem| let! $x:term := $e:term ; $body:doSeq) =>
  `(doElem| match ($e) with | $x => $body | _ => pure default)
| `(doElem| let! $x:term : $t:term := $e:term ; $body:doSeq) =>
  `(doElem| match ($e) with | ($x : $t) => $body | _ => pure default)
| `(doElem| let! $x:term := $e:term failwith $r:doSeq ; $body) =>
  `(doElem| match ($e) with | $x => $body | _ => $r)
| `(doElem| let! $x:term : $t:term := $e:term failwith $r:doSeq ; $body) =>
  `(doElem| match ($e) with | ($x : $t) => $body | _ => $r)
| `(doElem| let! $x:term ← $e:term ; $body) =>
  `(doElem| match ← $e with | $x => $body | _ => pure default)
| `(doElem| let! $x:term : $t:term ← $e:term ; $body) =>
  `(doElem| match ← $e with | ($x : $t) => $body | _ => pure default)
| `(doElem| let! $x:term ← $e:term failwith $r:doSeq ; $body) =>
  `(doElem| match ← $e with | $x => $body | _ => $r)
| `(doElem| let! $x:term : $t:term ← $e:term failwith $r:doSeq ; $body) =>
  `(doElem| match ← $e with | ($x : $t) => $body | _ => $r)

/-
#eval let! some x := some 42; some (x + 1)
#eval let! (_, some y) := (90, some 10)
      some (y * 3)
#eval let! [x] := [1]; some (x + 1)
#eval let! some x := none; some (x + 1)
#eval let! some _ : Option Nat := none; true
#eval let! some (_, y) := some (1, 2); some (y + 1)
-/
