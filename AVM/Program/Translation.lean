import AVM.Program
import AVM.Class.Translation
import AVM.Task.Translation

namespace AVM

def Program.compile {lab : Ecosystem.Label} (eco : Ecosystem lab) (prog : Program lab Unit) : Anoma.Program :=
  let task : Task :=
    Task.absorbParams prog.params fun vals =>
      Class.Program.tasks eco prog vals |>
        Task.compose
  task.toProgram
