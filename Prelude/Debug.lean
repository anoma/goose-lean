import Lean

open Lean

elab "here#" : term => do
  let file ← getFileName
  let ref ← getRef
  let some pos := ref.getPos?
    | return mkStrLit "<unknown position>"
  let fm ← getFileMap
  let lc := fm.toPosition pos
  return mkStrLit s!"{file}:{lc.line}:{lc.column}"

instance (priority := high) [Pure m] : Inhabited (ExceptT String m α) where
  default := pure (f := m) (throw here#)
