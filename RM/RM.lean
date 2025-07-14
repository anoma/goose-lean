namespace RM


-- TODO Hashes: have type classes instead of arbitrary `Type u`
def LogicRef : Type (u+1) := Type u
def LabelRef : Type (u+1) := Type u


/--
https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L28-L49
/// A resource that can be created and consumed
-/
structure Resource where
  /--
  This is the top-level reference to the logic of the resource, either
  - the "outer" logic, for the case of function privacy (FP)
  - the "actual" logic, w/o any FP guarantees
  > a succinct representation of the predicate associated with the resource
  https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L33-L34
  -/
  logicRef : LogicRef
  /--
  The `labelRef` is typically the hash of the actual label
  > specif[ication of] the fungibility domain for the resource
  https://github.com/anoma/arm-risc0/blob/6f66697c827f0cb6db0abcc5912ac98c1852c3de/arm/src/resource.rs#L35-L36
  -/
  labelRef : LabelRef

/--
-/
structure Piece where
-- TODO define the corresponding piece (and move it to the high-level RM)

def kindOf (x : Resource) : LogicRef × LabelRef := ⟨x.logicRef, x.labelRef⟩
