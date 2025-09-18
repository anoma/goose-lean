import AVM
import Applib.Surface.Object

namespace Applib

open AVM

structure Reference (C : Type) where
  objId : ObjectId
  deriving Inhabited, Repr, BEq

instance Reference.hasTypeRep {C : Type} [TypeRep C] : TypeRep (Reference C) where
  rep := Rep.composite "Reference" [TypeRep.rep C]

-- TODO better name?
structure ObjectReference {lab : Ecosystem.Label} (classId : lab.ClassId) : Type 1 where
  {type : Type}
  ref : Reference type
  [isObjectOf : IsObjectOf classId type]

end Applib

abbrev AVM.Ecosystem.Label.MultiMethodId.SelvesReferences
  {lab : Ecosystem.Label}
  (multiId : lab.MultiMethodId)
  : Type 1
  := Ecosystem.Label.MultiMethodId.Selves' multiId Applib.ObjectReference
