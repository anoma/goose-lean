import AVM

namespace Applib

open AVM

class IsObject (S : Type) where
  label : Ecosystem.Label
  classId : label.ClassId
  toObject : S → ObjectData classId.label
  fromObject : ObjectData classId.label → S
  left_inverse : fromObject ∘ toObject = id := by rfl
  right_inverse : toObject ∘ fromObject = id := by rfl

lemma IsObject.left_inverse' {S : Type} [i : IsObject S] (s : S)
  : i.fromObject (i.toObject s) = s := by
  rw [← Function.comp_apply (f := fromObject) (g := toObject)]
  rw [i.left_inverse]
  rfl

lemma IsObject.right_inverse' {S : Type} [i : IsObject S] (o : ObjectData i.classId.label)
  : i.toObject (i.fromObject o) = o := by
  rw [← Function.comp_apply (f := toObject) (g := fromObject)]
  rw [i.right_inverse]
  rfl

structure AnObjectType : Type 1 where
  ty : Type
  [isObject : IsObject ty]

structure AnObject : Type 1 where
  {ty : Type}
  [isObject : IsObject ty]
  obj : ty

def IsObject.toAnObject {cl : Type} [i : IsObject cl] (o : cl) : AnObject := ⟨o⟩

def AnObject.toSomeObject (g : AnObject) : SomeObjectData :=
  let i : IsObject g.ty := g.isObject
  (i.toObject g.obj).toSomeObjectData

instance {ty : Type} [IsObject ty] : CoeHead ty AnObject where
  coe (obj : ty) := {obj}
