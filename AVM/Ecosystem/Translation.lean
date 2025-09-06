import AVM.Ecosystem
import AVM.Ecosystem.AppData
import Prelude
import AVM.Class.Translation
import AVM.Logic
import AVM.Action

namespace AVM.Ecosystem

open AVM.Action

def MultiMethod.parseObjectArgs
  {lab : Ecosystem.Label}
  (consumed : List Anoma.Resource)
  (funId : lab.MultiMethodId)
  : Option funId.Selves
  :=
  let try consumedVec : Vector Anoma.Resource funId.numObjectArgs := consumed.toSizedVector
  let mkConsumedObject (a : funId.ObjectArgNames) : Option (Object a.classId.label) := Object.fromResource (consumedVec.get a.ix)
  @FinEnum.decImageOption'
    funId.ObjectArgNames
    (lab.objectArgNamesEnum funId)
    (fun a => Object a.classId.label)
    mkConsumedObject

def MultiMethod.logic
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Logic.Args)
  (funId : lab.MultiMethodId)
  (funData : MultiMethodData)
  (fargs : funId.Args.type)
  : Bool := sorry

private def logic
  {lab : Ecosystem.Label}
  (eco : Ecosystem lab)
  (args : Logic.Args)
  : Bool := sorry
