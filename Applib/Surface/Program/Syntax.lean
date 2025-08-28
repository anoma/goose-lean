import Applib.Surface.Program

namespace Applib

open Lean

declare_syntax_cat program

syntax withPosition(ident " := " " create " ident ident term) optSemicolon(program) : program
syntax withPosition("destroy " ident ident term) optSemicolon(program) : program
syntax withPosition("call " ident ident term) optSemicolon(program) : program
syntax withPosition(ident " := " " fetch " term) optSemicolon(program) : program
syntax "return " term : program
syntax "Ξ " ident* " . " program:40 : term
syntax "⟪" program "⟫" : term

def mkProducts {m} [Monad m] [MonadQuotation m] (ss : TSyntaxArray `ident) : m (TSyntax `term) := do
  let unit : TSyntax `term ← `(_)
  ss.foldrM (fun s acc => `(⟨$s, $acc⟩)) unit

macro_rules
  | `(⟪$p:program⟫) => `(Ξ . $p)
  | `(Ξ $ss:ident* . $x:ident := create $c:ident $m:ident $e:term ; $p:program) => do
    let ps ← mkProducts ss
    `(Program.create $c $m (fun $ps => $e) (Ξ $ss* $x . $p))
  | `(Ξ $ss:ident* . destroy $c:ident $m:ident $e:term $args:term ; $p:program) => do
    let ps ← mkProducts ss
    `(Program.destroy $c $m (fun $ps => $e) (fun $ps => $args) (Ξ $ss* . $p))
  | `(Ξ $ss:ident* . call $c:ident $m:ident $e:term $args:term ; $p:program) => do
    let ps ← mkProducts ss
    `(Program.call $c $m (fun $ps => $e) (fun $ps => $args) (Ξ $ss* . $p))
  | `(Ξ $ss:ident* . $x:ident := fetch $e:term ; $p:program) => do
    let ps ← mkProducts ss
    `(Program.fetch (fun $ps => $e) (Ξ $ss* $x . $p))
  | `(Ξ $ss:ident* . return $e:term) => do
    let ps ← mkProducts ss
    `(Program.return (fun $ps => $e))
