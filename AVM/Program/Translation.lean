import AVM.Program
import AVM.Ecosystem
import AVM.Tasks
import AVM.Task.Translation
import AVM.Class.Translation.Tasks

namespace AVM

def Program.compile {lab : Ecosystem.Label} (eco : Ecosystem lab) (prog : Program lab Unit) : Anoma.Program :=
  Member.Body.tasks eco prog.lift
    |>.void
    |>.compose
    |>.toProgram
