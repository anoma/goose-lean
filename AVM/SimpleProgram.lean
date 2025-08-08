import Prelude
import Anoma
import AVM.Object
import AVM.Message

namespace AVM

structure SimpleProgram (lab : Class.Label) where
  /-- List of objects to fetch by object uid. -/
  fetch : List Anoma.ObjectId
  message : Message lab
  actions : List Anoma.Action
