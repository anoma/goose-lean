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

structure AnObject : Type 1 where
  {ty : Type}
  [isObject : IsObject ty]
  obj : ty

def IsObject.toAnObject {cl : Type} [i : IsObject cl] (o : cl) : AnObject := ⟨o⟩

def AnObject.toSomeObjectData (g : AnObject) : SomeObjectData :=
  let i : IsObject g.ty := g.isObject
  (i.toObject g.obj).toSomeObjectData

instance {ty : Type} [IsObject ty] : CoeHead ty AnObject where
  coe (obj : ty) := {obj}

structure AnObjectOf {lab : Ecosystem.Label} (classId : lab.ClassId) : Type 1 where
  {ty : Type}
  [isObjectOf : IsObjectOf classId ty]
  obj : ty

def AnObjectOf.toObjectData {lab : Ecosystem.Label} {classId : lab.ClassId} (g : AnObjectOf classId) : ObjectData classId :=
  let i : IsObjectOf classId g.ty := g.isObjectOf
  i.toObject g.obj
