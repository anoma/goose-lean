import AVM

namespace Applib

open AVM

class IsObject (S : Type) where
  label : Ecosystem.Label
  classId : label.ClassId
  toObject : S → ObjectData classId.label
  fromObject : ObjectData classId.label → S
  left_inverse : fromObject ∘ toObject = id := by rfl

lemma IsObject.left_inverse' {S : Type} [i : IsObject S] (s : S)
  : i.fromObject (i.toObject s) = s := by
  rw [← Function.comp_apply (f := fromObject) (g := toObject)]
  rw [i.left_inverse]
  rfl
