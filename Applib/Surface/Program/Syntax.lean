import Applib.Surface.Program
import Apps.TwoCounter

namespace Applib

open Lean

declare_syntax_cat program

syntax "Ξ " ident* " . " program:40 : program
syntax withPosition("set " ident " := " " fetch " term) optSemicolon(program) : program
syntax withPosition("call " ident term) optSemicolon(program) : program
syntax "return " term : program
syntax (name := term_of_program) "⟪" program "⟫" : term

def mkProducts {m} [Monad m] [MonadQuotation m] (ss : TSyntaxArray `ident) : m (TSyntax `term) := do
  let unit : TSyntax `term ← `(_)
  ss.foldrM (fun s acc => `(⟨$s, $acc⟩)) unit

macro_rules
  | `(⟪Ξ $ss:ident* . set $x:ident := fetch $e:term ; $p:program⟫) => do
    let ps ← mkProducts ss
    let stx ← `(Program.fetch (fun $ps => $e) (⟪Ξ $ss* $x . $p⟫))
    dbg_trace Syntax.prettyPrint stx
    return stx
  | `(⟪Ξ $ss:ident* . return $e:term⟫) => do
    let stx ← `(Program.return (fun $ss* => $e))
    dbg_trace Syntax.prettyPrint stx
    return stx

open TwoCounterApp

def counterRef : Reference Counter := ⟨42⟩

-- set_option trace.Elab.step true

#check ⟪Ξ . set x := fetch counterRef; return x⟫
