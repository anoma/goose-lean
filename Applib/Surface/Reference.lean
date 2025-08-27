import AVM

namespace Applib

open AVM

structure Reference (C : Type) where
  objId : ObjectId
  deriving Inhabited, Repr, BEq

instance Reference.hasTypeRep {C : Type} [TypeRep C] : TypeRep (Reference C) where
  rep := Rep.composite "Reference" [TypeRep.rep C]
