import Mathlib.Data.FinEnum
import Lean
open Lean Elab Term Command
open Lean.Parser.Term

namespace FinEnum

/-- Produces a FinEnum instance for the given inductive.
It assumes that all constructors are nullary -/
def derive (declNames : Array Name) : CommandElabM Bool :=
  match declNames with
  | #[d] => do
    let env ← getEnv
    match env.find? d with
    | some (.inductInfo ind) => do
      let mut constructors : Array (TSyntax `term) := #[]
      for constructor_name in ind.ctors do
        let c := mkIdent constructor_name
        constructors := constructors.push (← `($c))
      let instance_cmd ← `(instance : FinEnum $(mkIdent d) :=
                        FinEnum.ofList [ $[$constructors],* ]
                        fun x => by cases x <;> simp)
      elabCommand instance_cmd
      return true
    | _ => return false
  | _ => return false

initialize registerDerivingHandler ``FinEnum derive

/-- Standalone instance of FinEnum -/
elab "#FinEnum.derive" name:ident : command => do
  if ← derive #[name.getId] then
    pure ()
  else
    throwError "Failed to derive FinEnum for {name.getId}"
