import AVM

namespace Applib

open AVM

class IsObjectOf {lab : Ecosystem.Label} (classId : lab.ClassId) (S : Type) where
  toObject : S → ObjectData classId
  fromObject : ObjectData classId → S
  left_inverse : fromObject ∘ toObject = id := by rfl

class IsObject (S : Type) where
  label : Ecosystem.Label
  classId : label.ClassId
  isObjectOf : IsObjectOf classId S

abbrev IsObject.toObject {S} (i : IsObject S) : S → ObjectData i.classId := i.isObjectOf.toObject

abbrev IsObject.fromObject {S} (i : IsObject S) : ObjectData i.classId → S := i.isObjectOf.fromObject

lemma IsObjectOf.left_inverse'
  {lab : Ecosystem.Label}
  {classId : lab.ClassId}
  {S : Type}
  [i : IsObjectOf classId S]
  (s : S)
  : i.fromObject (i.toObject s) = s := by
  rw [← Function.comp_apply (f := fromObject) (g := toObject)]
  rw [i.left_inverse]
  rfl
