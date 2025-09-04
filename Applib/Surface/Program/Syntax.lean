import Applib.Surface.Program

namespace Applib

open Lean

declare_syntax_cat program

syntax withPosition("create " ident ident term) optSemicolon(program) : program
syntax withPosition(ident " := " " create " ident ident term) optSemicolon(program) : program
syntax withPosition("destroy " ident term) optSemicolon(program) : program
syntax withPosition("call " ident term) optSemicolon(program) : program
syntax withPosition(ident " := " " fetch " term) optSemicolon(program) : program
syntax "return " term : program
syntax "⟪" program "⟫" : term

macro_rules
  | `(⟪create $c:ident $m:ident $e:term ; $p:program⟫) => do
    `(Program.create' $c $m $e (fun _ => ⟪$p⟫))
  | `(⟪$x:ident := create $c:ident $m:ident $e:term ; $p:program⟫) => do
    `(Program.create' $c $m $e (fun $x => ⟪$p⟫))
  | `(⟪destroy $m:ident $e:term $args:term ; $p:program⟫) => do
    `(Program.destroy' $e $m $args ⟪$p⟫)
  | `(⟪call $m:ident $e:term $args:term ; $p:program⟫) => do
    `(Program.call' $e $m $args ⟪$p⟫)
  | `(⟪$x:ident := fetch $e:term ; $p:program⟫) => do
    `(Program.fetch' $e (fun $x => ⟪$p⟫))
  | `(⟪return $e:term⟫) => do
    `(Program.return $e)
