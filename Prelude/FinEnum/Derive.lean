import Mathlib.Data.FinEnum
import Lean
open Lean Elab Parser Term Command

namespace FinEnum

def derive (declNames : Array Name) : CommandElabM Bool :=
  match declNames with
  | #[d] => do
    let env ← getEnv
    match env.find? d with
    | some (.inductInfo ind) => do
      let mut mem_proofs : Array (TSyntax ``matchAlt) := #[]
      let mut constructors : Array (TSyntax `term) := #[]
      for constructor_name in ind.ctors do
        let c := mkIdent constructor_name
        constructors := constructors.push (← `($c))
        mem_proofs := mem_proofs.push (← `(matchAltExpr| | $c => by simp))
      let instance_cmd ← `(instance : FinEnum $(mkIdent d) :=
                        FinEnum.ofList [ $[$constructors],* ]
                        fun x => match x with $mem_proofs:matchAlt*)
      elabCommand instance_cmd
      return true
    | _ => return false
  | _ => return false

initialize registerDerivingHandler ``FinEnum derive
