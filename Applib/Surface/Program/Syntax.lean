import Applib.Surface.Program

namespace Applib

open Lean

declare_syntax_cat program

syntax colEq withPosition("if " term " then " colGt withPosition(program)) withPosition(" else " colGt withPosition(program)) : program
syntax colEq withPosition("if " term " then " colGt withPosition(program)) withPosition(" else " colGt withPosition(program)) optSemicolon(program) : program
syntax colEq withPosition("create " ident ident term) optSemicolon(program) : program
syntax colEq withPosition(ident " := " " create " ident ident term) optSemicolon(program) : program
syntax colEq withPosition("destroy " ident term) optSemicolon(program) : program
syntax colEq "call " ident term : program
syntax colEq withPosition("call " ident term) optSemicolon(program) : program
syntax colEq withPosition("invoke " term) optSemicolon(program) : program
syntax colEq withPosition(ident " := " " invoke " term) optSemicolon(program) : program
syntax colEq withPosition(ident " := " " fetch " term) optSemicolon(program) : program
syntax colEq "return " term : program
syntax "⟪" program "⟫" : term

macro_rules
  | `(⟪if $cond:term then $thenProg:program else $elseProg:program⟫) => do
    `(if $cond then ⟪$thenProg⟫ else ⟪$elseProg⟫)
  | `(⟪if $cond:term then $thenProg:program else $elseProg:program ; $p:program⟫) => do
    `(let next := fun _ => ⟪$p⟫; if $cond then Program.invoke ⟪$thenProg⟫ next else Program.invoke ⟪$elseProg⟫ next)
  | `(⟪create $c:ident $m:ident $e:term ; $p:program⟫) => do
    `(Program.create' $c $m $e (fun _ => ⟪$p⟫))
  | `(⟪$x:ident := create $c:ident $m:ident $e:term ; $p:program⟫) => do
    `(Program.create' $c $m $e (fun $x => ⟪$p⟫))
  | `(⟪destroy $m:ident $e:term $args:term ; $p:program⟫) => do
    `(Program.destroy' $e $m $args (⟪$p⟫))
  | `(⟪call $m:ident $e:term $args:term⟫) => do
    `(Program.call' $e $m $args (Program.return ()))
  | `(⟪call $m:ident $e:term $args:term ; $p:program⟫) => do
    `(Program.call' $e $m $args (⟪$p⟫))
  | `(⟪invoke $e:term ; $p:program⟫) => do
    `(Program.invoke $e (fun _ => ⟪$p⟫))
  | `(⟪$x:ident := invoke $e:term ; $p:program⟫) => do
    `(Program.invoke $e (fun $x => ⟪$p⟫))
  | `(⟪$x:ident := fetch $e:term ; $p:program⟫) => do
    `(Program.fetch' $e (fun $x => ⟪$p⟫))
  | `(⟪return $e:term⟫) => do
    `(Program.return $e)
