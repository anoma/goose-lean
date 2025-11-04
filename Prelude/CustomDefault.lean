import Lean
import Prelude.Debug

open Lean
open Elab.Tactic Meta

elab "mydefault" : tactic => do
   let tgt ← getMainTarget
   if tgt.isAppOf `Anoma.LogicM
     then
        let rawErr : TSyntax `term := mkIdent `Anoma.LogicM.Error.onlyPosition
        let t ← `(tactic| exact (throw ($rawErr here#)))
        evalTactic t
     else do
      let t ← `(tactic| exact default)
      evalTactic t

elab "mydefaultM" : tactic => do
   let tgt ← getMainTarget
   if tgt.isAppOf `LogicM
     then
        let t ← `(tactic| exact (throw (LogicM.Error.onlyPosition here#)))
        evalTactic t
     else do
      let t ← `(tactic| exact (pure default))
      evalTactic t
