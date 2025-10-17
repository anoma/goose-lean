namespace Hashable

structure MixState : Type where
  hash : UInt64

abbrev MixState.empty : MixState where
  hash := Hashable.hash Unit.unit

/-- A monad for conveniently mixing hashes with do-notation. -/
abbrev Mix : Type := StateM MixState Unit

def Mix.mix {α : Type u} [Hashable α] (a : α) : Mix :=
  modify (fun s => { s with hash := mixHash s.hash (hash a) })

def Mix.run (m : Mix) : UInt64 := StateT.run m MixState.empty |>.snd.hash

end Hashable

export Hashable.Mix (mix)
