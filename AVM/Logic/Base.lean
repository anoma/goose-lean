import Anoma
import AVM.Ecosystem.Label.Base
import AVM.Action.DummyResource

namespace AVM.Logic

def classLogicRef {lab : Ecosystem.Label} (classId : lab.ClassId) : Anoma.LogicRef :=
  classId.label.logicRef

def trivialLogicRef : Anoma.LogicRef := Anoma.LogicRef.mk "Anoma.TrivialLogic"

def trivialLogic : Anoma.Logic :=
  { reference := trivialLogicRef,
    function := fun _ => .true }
