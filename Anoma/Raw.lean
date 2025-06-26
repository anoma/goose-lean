
namespace Anoma

/-- Typeclass for types that can be serialized to a unique "raw" representation.
    Equality on representations should imply equality of the corresponding
    values, regardless of their types – we can compare values of different
    types via their representations. -/
class Raw (α : Type u) where
  raw : α → String
  cooked : String -> Option α

instance (α : Type u) [ToString α] : Raw α where
  raw a := toString a
  cooked := panic! "cooked"

def rawEq {α β} [Raw α] [Raw β] (a : α) (b : β) : Bool :=
  Raw.raw a == Raw.raw b

end Anoma
