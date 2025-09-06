import AVM.Ecosystem
import Prelude
import AVM.Class.Translation
import AVM.Logic
import AVM.Action

namespace AVM.Ecosystem

open AVM.Action

def Function.parseObjectArgs
  {lab : Ecosystem.Label}
  (consumed : List Anoma.Resource)
  (funId : lab.FunctionId)
  : Option funId.Selves
  :=
  let try consumedVec : Vector Anoma.Resource funId.numObjectArgs := consumed.toSizedVector
  let mkConsumedObject (a : funId.ObjectArgNames) : Option (Object a.classId.label) := Object.fromResource (consumedVec.get a.ix)
  @FinEnum.decImageOption'
        funId.ObjectArgNames
        (lab.objectArgNamesEnum funId)
        (fun a => Object a.classId.label)
        mkConsumedObject
