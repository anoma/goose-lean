import Lean.Parser.Term
import Prelude.CustomDefault
import Lean

open Lean.Parser.Term

syntax withPosition("check" term) optSemicolon(term)? : term
syntax withPosition("check " binderIdent " : " term) optSemicolon(term) : term
syntax withPosition("check" term) optSemicolon(doSeq) : doElem
syntax withPosition("check " binderIdent " : " term) optSemicolon(doSeq) : doElem

syntax withPosition("check" term) withPosition("failwith" term) optSemicolon(term)? : term
syntax withPosition("check " binderIdent " : " term) withPosition("failwith" term) optSemicolon(term) : term
syntax withPosition("check" term) withPosition("failwith" doSeq) optSemicolon(doSeq) : doElem
syntax withPosition("check " binderIdent " : " term) withPosition("failwith" doSeq) optSemicolon(doSeq) : doElem

/-- The `check a; b` macro returns `b` if `a` evaluates to `true`, or `default`
  otherwise. -/
macro_rules
| `(check $cond:term ; $body:term) =>
  `(if $cond then $body else by mydefault)
| `(check $h:ident : $cond:term ; $body:term) =>
  `(if $h:ident : $cond then $body else by mydefault)
| `(check $cond:term) =>
  `($cond)
| `(doElem| check $cond:term ; $body:doSeq) =>
  `(doElem| if $cond then $body else by mydefaultM)
| `(doElem| check $h:ident : $cond:term ; $body:doSeq) =>
  `(doElem| if $h : $cond then $body else by mydefaultM)

| `(check $cond:term failwith $f:term ; $body:term) =>
  `(if $cond then $body else $f)
| `(check $h:ident : $cond:term failwith $f:term ; $body:term) =>
  `(if $h:ident : $cond then $body else $f)
| `(check $cond:term failwith $f) =>
  `(if $cond then true else $f)
| `(doElem| check $cond:term failwith $f:doSeq ; $body:doSeq) =>
  `(doElem| if $cond then $body else $f)
| `(doElem| check $h:ident : $cond:term failwith $f:doSeq ; $body:doSeq) =>
  `(doElem| if $h : $cond then $body else $f)
