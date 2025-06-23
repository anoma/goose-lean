
namespace Anoma

class Raw (α : Type u) where
  raw : α → String

instance (α : Type u) [ToString α] : Raw α where
  raw a := toString a

def rawEq {α β} [Raw α] [Raw β] (a : α) (b : β) : Bool :=
  Raw.raw a == Raw.raw b

end Anoma
