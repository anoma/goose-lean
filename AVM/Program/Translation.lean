import AVM.Program
import AVM.Ecosystem
import AVM.Tasks
import AVM.Task.Translation
import AVM.Class.Translation.Tasks

namespace AVM

def Program.compile {lab : Scope.Label} (scope : Scope lab) (prog : Program lab Unit) : Anoma.Program :=
  Member.Body.tasks scope prog.lift
    |>.void
    |>.compose
    |>.toProgram
