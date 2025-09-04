import Applib.Surface.Program

namespace Applib

open Lean

declare_syntax_cat program

syntax withPosition("create " ident ident term) optSemicolon(program) : program
syntax withPosition(ident " := " " create " ident ident term) optSemicolon(program) : program
syntax withPosition("destroy " ident term) optSemicolon(program) : program
syntax withPosition("call " ident term) optSemicolon(program) : program
syntax withPosition("invoke " term) optSemicolon(program) : program
syntax withPosition(ident " := " " invoke " term) optSemicolon(program) : program
syntax withPosition(ident " := " " fetch " term) optSemicolon(program) : program
syntax "return " term : program
syntax "Ξ " program : term
syntax "⟪" program "⟫" : term

macro_rules
  | `(⟪$p:program⟫) => do
    `(Program.Sized.toProgram (Ξ $p))
  | `(Ξ create $c:ident $m:ident $e:term ; $p:program) => do
    `(Program.Sized.create' $c $m $e (fun _ => Ξ $p))
  | `(Ξ $x:ident := create $c:ident $m:ident $e:term ; $p:program) => do
    `(Program.Sized.create' $c $m $e (fun $x => Ξ $p))
  | `(Ξ destroy $m:ident $e:term $args:term ; $p:program) => do
    `(Program.Sized.destroy' $e $m $args (Ξ $p))
  | `(Ξ call $m:ident $e:term $args:term ; $p:program) => do
    `(Program.Sized.call' $e $m $args (Ξ $p))
  | `(Ξ invoke $e:term ; $p:program) => do
    `(Program.Sized.invoke' $e (fun _ => Ξ $p))
  | `(Ξ $x:ident := invoke $e:term ; $p:program) => do
    `(Program.Sized.invoke' $e (fun $x => Ξ $p))
  | `(Ξ $x:ident := fetch $e:term ; $p:program) => do
    `(Program.Sized.fetch' $e (fun $x => Ξ $p))
  | `(Ξ return $e:term) => do
    `(Program.Sized.return' $e)
