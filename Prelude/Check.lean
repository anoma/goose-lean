syntax withPosition("check" term) optSemicolon(term) : term
syntax withPosition("check" term) optSemicolon(doSeq) : doElem

/-- The `check a; b` macro returns `default` if `a` evaluates to `false`, or `b` if
  `a` evaluates to `true`. -/
macro_rules
| `(check $cond:term ; $body:term) =>
  `(if $cond then $body else default)
| `(doElem| check $cond:term ; $body:doSeq) =>
  `(doElem| if $cond then $body else pure default)
