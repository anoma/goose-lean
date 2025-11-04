import Prelude.Macro
import Prelude.CustomDefault

syntax withPosition("check" term) optSemicolon(term)? : term
syntax withPosition("check " binderIdent " : " term) optSemicolon(term) : term
syntax withPosition("check" term) optSemicolon(doSeq) : doElem
syntax withPosition("check " binderIdent " : " term) optSemicolon(doSeq) : doElem

syntax withPosition("check" term) withPosition("failwith" term) optSemicolon(term)? : term
syntax withPosition("check " binderIdent " : " term) withPosition("failwith" term) optSemicolon(term) : term
syntax withPosition("check" term) withPosition("failwith" term) optSemicolon(doSeq) : doElem

syntax withPosition("docheck " binderIdent " : " term) withPosition("failwith" term) optSemicolon(doSeq) : doElem
syntax withPosition("docheck" term) optSemicolon(doSeq) : doElem
syntax withPosition("docheck " binderIdent " : " term) optSemicolon(doSeq) : doElem
syntax withPosition("docheck" term) withPosition("failwith" term) optSemicolon(doSeq) : doElem


/-- The `check a; b` macro returns `b` if `a` evaluates to `true`, or `default`
  otherwise. -/
macro_rules
| `(check $cond:term ; $body:term) =>
  `(if $cond then $body else by mydefault)
| `(check $h:ident : $cond:term ; $body:term) =>
  `(if $h:ident : $cond then $body else by mydefault)
| `(check $cond:term) =>
  `($cond)
| `(doElem| docheck $cond:term ; $body:doSeq) =>
  `(doElem| if $cond then $body else by mydefaultM)
| `(doElem| docheck $h:ident : $cond:term ; $body:doSeq) =>
  `(doElem| if $h : $cond then $body else by mydefaultM)

| `(check $cond:term failwith $f:term ; $body:term) =>
  `(if $cond then $body else $f)
| `(check $h:ident : $cond:term failwith $f:term ; $body:term) =>
  `(if $h:ident : $cond then $body else $f)
| `(check $cond:term failwith $f) =>
  `(if $cond then true else $f)
| `(doElem| docheck $cond:term failwith $f:term ; $body:doSeq) => do
  let errDo : TSyntax `Lean.Parser.Term.doSeq ← doSeq1 (← `(term| $f))
  `(doElem| if $cond then $body else $errDo)
| `(doElem| docheck $h:ident : $cond:term failwith $f:term ; $body:doSeq) => do
  let errDo : TSyntax `Lean.Parser.Term.doSeq ← doSeq1 (← `(term| $f))
  `(doElem| if $h : $cond then $body else $errDo)

example [Monad m] : m Unit := do
  docheck 0 == 0
  pure .unit
