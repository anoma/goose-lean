import AVM.Program
import AVM.Class.Translation
import AVM.Task.Translation

namespace AVM

def Program.compile {lab : Ecosystem.Label} (eco : Ecosystem lab) (prog : Program lab Unit) : Anoma.Program :=
  Class.Member.Body.tasks eco prog |> Tasks.compose |>.toProgram
