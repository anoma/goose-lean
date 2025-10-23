import Lean
import Prelude.Debug

open Lean
open Elab.Tactic Meta

elab "mydefault" : tactic => do
   let tgt ← getMainTarget
   -- logInfo s!"unchecked default {tgt}"
   if tgt.isAppOf `Anoma.LogicM
     then
        -- logInfo "XXXXXXXX unchecked default"
        let rawErr : TSyntax `term := mkIdent `Anoma.Logic.Error.rawError
        let t ← `(tactic| exact (throw ($rawErr here#)))
        evalTactic t
     else do
      let t ← `(tactic| exact default)
      evalTactic t

elab "mydefaultM" : tactic => do
   let tgt ← getMainTarget
   -- logInfo "mydefaultM"
   if tgt.isAppOf `LogicM
     then
        -- logInfo "MMMMMMM  unchecked default M"
        let t ← `(tactic| exact (throw here#))
        evalTactic t
     else do
      let t ← `(tactic| exact (pure default))
      evalTactic t
