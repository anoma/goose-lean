class HBeq (α β : Type u) where
  hbeq : α → β → Bool

infix:50 " ≍? " => HBeq.hbeq

instance BEq.instHBEq (α : Type u) [BEq α] : HBeq α α where
  hbeq a b := a == b

class ReflHBeq (α : Type u) [HBeq α α] : Prop where
  rfl {a : α} : a ≍? a

class LawfulHBeq (α β : Type u) [HBeq α β] : Prop where
  heq_of_hbeq {a : α} {b : β} : a ≍? b → a ≍ b
