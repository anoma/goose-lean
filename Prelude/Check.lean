syntax withPosition("check" term) optSemicolon(term)? : term
syntax withPosition("check" term) optSemicolon(doSeq) : doElem

/-- The `check a; b` macro returns `b` if `a` evaluates to `true`, or `default`
  otherwise. -/
macro_rules
| `(check $cond:term ; $body:term) =>
  `(if $cond then $body else default)
| `(check $cond:term) =>
  `($cond)
| `(doElem| check $cond:term ; $body:doSeq) =>
  `(doElem| if $cond then $body else pure default)
