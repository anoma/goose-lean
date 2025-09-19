class HBEq (α β : Type u) where
  hbeq : α → β → Bool

/-- Heterogeneous boolean equality. -/
infix:50 " ≍? " => HBEq.hbeq

instance BEq.instHBEq (α : Type u) [BEq α] : HBEq α α where
  hbeq a b := a == b

class ReflHBEq (α : Type u) [HBEq α α] : Prop where
  rfl {a : α} : a ≍? a

class LawfulHBEq (α β : Type u) [HBEq α β] : Prop where
  heq_of_hbeq {a : α} {b : β} : a ≍? b → a ≍ b
