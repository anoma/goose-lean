import Lean

open Lean

structure FilePosition where
  file : String
  pos : Position
  deriving ToExpr

instance : Repr FilePosition where
  reprPrec p _ := s!"{p.file}:{p.pos.line}:{p.pos.column}"

def FilePosition.unknown : FilePosition where
  file := "<unknown-file>"
  pos := ⟨0, 0⟩

-- returns FilePosition for the location where it is inserted
elab "here#" : term => do
  let file ← getFileName
  let ref ← getRef
  let fm ← getFileMap
  let some pos := ref.getPos?
    | return (toExpr FilePosition.unknown)
  let lc : FilePosition :=
         { file
           pos := fm.toPosition pos }
  return (toExpr lc)
