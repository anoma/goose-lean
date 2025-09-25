import Applib.Surface.Program
import Applib.Surface.Member

namespace Applib

open Lean

declare_syntax_cat program
declare_syntax_cat branch_body

def matchAltsParser : Parser.Parser :=
  Lean.Parser.Term.matchAlts (Lean.Parser.withPosition (Lean.Parser.categoryParser `branch_body 0))

syntax program : branch_body
syntax colGe withPosition("let" term (":" term)? ":=" term) optSemicolon(program) : program
syntax colGe withPosition("match " term,+ " with " ppLine colGe matchAltsParser) : program
syntax colGe withPosition("match " term,+ " with " ppLine colGe matchAltsParser) optSemicolon(program) : program
syntax colGe withPosition("if " term " then " colGt withPosition(program)) colGe withPosition(" else " colGt withPosition(program)) : program
syntax colGe withPosition("if " term " then " colGt withPosition(program)) colGe withPosition(" else " colGt withPosition(program)) optSemicolon(program) : program
syntax colGe withPosition("if " term " then " colGt withPosition(program)) : program
syntax colGe withPosition("if " term " then " colGt withPosition(program)) optSemicolon(program) : program
syntax colGe "create " ident ident term : program
syntax colGe "create " ident ident term " signed " term : program
syntax colGe withPosition("create " ident ident term) optSemicolon(program) : program
syntax colGe withPosition("create " ident ident term " signed " term) optSemicolon(program) : program
syntax colGe withPosition(ident " := " " create " ident ident term) optSemicolon(program) : program
syntax colGe withPosition(ident " := " " create " ident ident term " signed " term) optSemicolon(program) : program
syntax colGe "destroy " ident term : program
syntax colGe "destroy " ident term " signed " term : program
syntax colGe withPosition("destroy " ident term) optSemicolon(program) : program
syntax colGe withPosition("destroy " ident term " signed " term) optSemicolon(program) : program
syntax colGe "call " ident term : program
syntax colGe "call " ident term " signed " term : program
syntax colGe withPosition("call[" term "] " ident term) optSemicolon(program) : program
syntax colGe withPosition("call " ident term " signed " term) optSemicolon(program) : program
syntax colGe "multiCall " ident term : program
syntax colGe "multiCall " ident term " signed " term : program
syntax colGe withPosition("multiCall " ident term) optSemicolon(program) : program
syntax colGe withPosition("multiCall " ident term " signed " term) optSemicolon(program) : program
syntax colGe "upgrade " term " to " term : program
syntax colGe withPosition("upgrade " term " to " term) optSemicolon(program) : program
syntax colGe "invoke " term : program
syntax colGe withPosition("invoke " term) optSemicolon(program) : program
syntax colGe withPosition(ident " := " " invoke " term) optSemicolon(program) : program
syntax colGe withPosition(ident " := " " fetch " term) optSemicolon(program) : program
syntax colGe "return " term : program
syntax colGe "!" term : program
syntax "⟪" withPosition(program) "⟫" : term

macro_rules
  | `(branch_body| $p:program) =>
    `(⟪$p⟫)
  | `(⟪let $x:term := $e:term ; $p:program⟫) =>
    `(let ($x) := $e ; ⟪$p⟫)
  | `(⟪let $x:term : $ty:term := $e:term ; $p:program⟫) =>
    `(let ($x) : $ty := $e ; ⟪$p⟫)
  | `(⟪match $es:term with $alts⟫) =>
    `(match $es:term with $alts)
  | `(⟪match $es:term with $alts ; $p:program⟫) =>
    `(Program.invoke (match $es:term with $alts) (fun _ => ⟪$p⟫))
  | `(⟪if $cond:term then $thenProg:program else $elseProg:program⟫) =>
    `(if $cond then ⟪$thenProg⟫ else ⟪$elseProg⟫)
  | `(⟪if $cond:term then $thenProg:program else $elseProg:program ; $p:program⟫) =>
    `(let next := fun _ => ⟪$p⟫; if $cond then Program.invoke ⟪$thenProg⟫ next else Program.invoke ⟪$elseProg⟫ next)
  | `(⟪if $cond:term then $thenProg:program⟫) =>
    `(if $cond then ⟪$thenProg⟫ else Program.return ())
  | `(⟪if $cond:term then $thenProg:program ; $p:program⟫) =>
    `(let next := fun () => ⟪$p⟫; if $cond then Program.invoke ⟪$thenProg⟫ next else next ())
  | `(⟪create $c:ident $m:ident $e:term ⟫) =>
    `(Program.create' $c $m $e unsigned Program.return)
  | `(⟪create $c:ident $m:ident $e:term signed $signatures:term⟫) =>
    `(Program.create' $c $m $e $signatures Program.return)
  | `(⟪create $c:ident $m:ident $e:term; $p:program⟫) =>
    `(Program.create' $c $m $e unsigned (fun _ => ⟪$p⟫))
  | `(⟪create $c:ident $m:ident $e:term signed $signatures:term; $p:program⟫) =>
    `(Program.create' $c $m $e $signatures (fun _ => ⟪$p⟫))
  | `(⟪$x:ident := create $c:ident $m:ident $e:term; $p:program⟫) =>
    `(Program.create' $c $m $e unsigned (fun $x => ⟪$p⟫))
  | `(⟪$x:ident := create $c:ident $m:ident $e:term signed $signatures:term; $p:program⟫) =>
    `(Program.create' $c $m $e $signatures (fun $x => ⟪$p⟫))
  | `(⟪destroy $m:ident $e:term $args:term⟫) =>
    `(Program.destroy' $e $m $args unsigned (Program.return ()))
  | `(⟪destroy $m:ident $e:term $args:term signed $signatures:term⟫) =>
    `(Program.destroy' $e $m $args $signatures (Program.return ()))
  | `(⟪destroy $m:ident $e:term $args:term; $p:program⟫) =>
    `(Program.destroy' $e $m $args unsigned (⟪$p⟫))
  | `(⟪destroy $m:ident $e:term $args:term signed $signatures:term; $p:program⟫) =>
    `(Program.destroy' $e $m $args $signatures (⟪$p⟫))
  | `(⟪call $m:ident $e:term $args:term⟫) =>
    `(Program.call' $e $m $args unsigned (Program.return ()))
  | `(⟪call $m:ident $e:term $args:term signed $signatures⟫) =>
    `(Program.call' $e $m $args $signatures (Program.return ()))
  | `(⟪call[$eid:term] $m:ident $e:term $args:term ; $p:program⟫) =>
    `(Program.call' (inScope := {eid := $eid}) $e $m $args unsigned (⟪$p⟫))
  | `(⟪call $m:ident $e:term $args:term signed $signatures ; $p:program⟫) =>
    `(Program.call' $e $m $args $signatures (⟪$p⟫))
  | `(⟪multiCall $m:ident $selves:term $args:term⟫) =>
    `(Program.multiCall' $m $selves $args unsigned (Program.return ()))
  | `(⟪multiCall $m:ident $selves:term $args:term signed $signatures:term; $p:program⟫) =>
    `(Program.multiCall' $m $selves $args $signatures $signatures (⟪$p⟫))
  | `(⟪multiCall $m:ident $selves:term $args:term; $p:program⟫) =>
    `(Program.multiCall' $m $selves $args unsigned (⟪$p⟫))
  | `(⟪multiCall $m:ident $selves:term $args:term signed $signatures:term⟫) =>
    `(Program.multiCall' $m $selves $args $signatures (Program.return ()))
  | `(⟪upgrade $e:term to $e':term⟫) =>
    `(Program.upgrade' $e $e' Program.return)
  | `(⟪upgrade $e:term to $e':term ; $p:program⟫) =>
    `(Program.upgrade' $e $e' (⟪$p⟫))
  | `(⟪invoke $e:term⟫) =>
    `(Program.invoke $e Program.return)
  | `(⟪invoke $e:term ; $p:program⟫) =>
    `(Program.invoke $e (fun _ => ⟪$p⟫))
  | `(⟪$x:ident := invoke $e:term ; $p:program⟫) =>
    `(Program.invoke $e (fun $x => ⟪$p⟫))
  | `(⟪$x:ident := fetch $e:term ; $p:program⟫) =>
    `(Program.fetch' $e (fun $x => ⟪$p⟫))
  | `(⟪return $e:term⟫) =>
    `(Program.return $e)
  | `(⟪ ! $e:term⟫) =>
    `($e)
