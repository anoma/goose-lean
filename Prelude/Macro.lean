import Lean.Parser.Do
import Lean.Parser.Term

open Lean
open Parser
open Term

/-- Turn a `term` into a single-element `doSeq`. -/
def doSeq1 (t : TSyntax `term) : MacroM (TSyntax ``doSeq) :=
  `(doSeq| $t:term)

export Lean (TSyntax)
export Term (binderIdent)
