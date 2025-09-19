namespace ULift

instance instInhabited {α : Type u} [Inhabited α] : Inhabited (ULift α) where
  default := ULift.up default
