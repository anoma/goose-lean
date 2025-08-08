syntax withPosition("check" term) optSemicolon(term) : term
syntax withPosition("checkM" term) optSemicolon(doSeq) : doElem

/-- The `check a; b` macro returns `default` if `a` evaluates to `false`, or `b` if
  `a` evaluates to `true`. -/
macro_rules
| `(check $cond:term ; $body) =>
  `(if $cond then $body else default)

macro_rules
| `(doElem| checkM $cond:term ; $body) =>
  `(doElem| if $cond then $body else default)
