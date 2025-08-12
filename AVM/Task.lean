import Prelude
import Mathlib.Data.Prod.TProd
import Anoma
import AVM.Object
import AVM.Message

namespace AVM

structure Task.Parameter where
  uid : ObjectId
  classLabel : Class.Label

def Task.Parameter.Product (params : List Task.Parameter) : Type :=
  List.TProd (fun p : Task.Parameter => Object p.classLabel) params

structure Task where
  /-- Task parameters - objects to fetch from the Anoma system. -/
  params : List Task.Parameter
  /-- The message to send to the recipient. -/
  message : SomeMessage
  /-- Task actions - actions to perform parameterised by fetched objects. -/
  actions : Task.Parameter.Product params → List Anoma.Action
