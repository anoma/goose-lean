import Lean
import Prelude.LetTry

instance {α β} [Hashable α] [BEq α] [BEq β] : BEq (Std.HashMap α β) where
  beq m1 m2 :=
    m1.size == m2.size &&
    m1.toList.foldr (init := true) fun (k, v) acc =>
      let try v2 := m2.get? k
      acc && v == v2
