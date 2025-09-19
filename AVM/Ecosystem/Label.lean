import AVM.Ecosystem.Label.Base
import AVM.Object

namespace AVM.Ecosystem.Label.MultiMethodId

abbrev Selves' {lab : Ecosystem.Label} (multiId : lab.MultiMethodId) (f : lab.ClassId → Type u) : Type u :=
  (argName : multiId.ObjectArgNames) → f (lab.MultiMethodObjectArgClass argName)

abbrev Selves {lab : Ecosystem.Label} (multiId : lab.MultiMethodId) : Type := Selves' multiId Object

def ConsumedToSelves
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (consumed : List Anoma.Resource)
  : Option multiId.Selves
  :=
  let try consumedVec : Vector Anoma.Resource multiId.numObjectArgs := consumed.toSizedVector
  let mkConsumedObject (a : multiId.ObjectArgNames) : Option (Object a.classId) := Object.fromResource (consumedVec.get a.ix)
  @FinEnum.decImageOption'
    multiId.ObjectArgNames
    multiId.ObjectArgNamesEnum
    (fun a => Object a.classId)
    mkConsumedObject

def SelvesFromHList
  {lab : Ecosystem.Label}
  (multiId : lab.MultiMethodId)
  (l : HList (multiId.argsClassesVec.toList.map Object))
  : multiId.Selves := fun arg => by
  simp [argsClassesVec, List.Vector.toList_ofFn, List.map_ofFn] at l
  unfold Function.comp at l
  simp at l
  let enum := lab.ObjectArgNamesEnum multiId
  let elem := l.get (by
                  refine (enum.equiv.toFun arg).cast ?_
                  simp [List.length_ofFn]
                  rfl)
  exact (Eq.mp (by simp) elem)

def SelvesToVector
  {A : Type u}
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (selves : multiId.Selves)
  (f : {arg : multiId.ObjectArgNames} → Object arg.classId → A)
  : List.Vector A multiId.numObjectArgs
  := multiId.objectArgNamesVec.map (fun a => f (selves a))

abbrev SelvesIds
  {lab : Ecosystem.Label}
  (multiId : lab.MultiMethodId)
  : Type :=
  Selves' multiId (fun _ => ObjectId)

def SelvesIdsToVector
  {lab : Ecosystem.Label}
  {multiId : lab.MultiMethodId}
  (selvesIds : multiId.SelvesIds)
  : List.Vector ObjectId multiId.numObjectArgs :=
  List.Vector.ofFn (fun i => selvesIds (multiId.ObjectArgNamesEnum.equiv.invFun i))
