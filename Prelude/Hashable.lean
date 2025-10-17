import Std.Data.HashMap.Basic

instance {α : Type u} [Hashable α] : Hashable (ULift.{v} α) where
  hash d := hash d.down

instance {α β : Type u} [BEq α] [Hashable α] [Hashable β] : Hashable (Std.HashMap α β) where
  hash m := m.toList |>.map hash |>.mergeSort |> hash
