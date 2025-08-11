import Prelude
import Mathlib.Data.Prod.TProd
import Anoma
import AVM.Object
import AVM.Message

namespace AVM

structure Task.Parameter where
  id : ObjectId
  classLabel : Class.Label

def Task.Parameter.type (params : List Task.Parameter) : Type :=
  List.TProd (fun p : Task.Parameter => Object p.classLabel) params

structure Task (lab : Class.Label) where
  params : List Task.Parameter
  message : Message lab
  actions : Task.Parameter.type params → List Anoma.Action
