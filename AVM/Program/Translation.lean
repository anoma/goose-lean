import AVM.Program
import AVM.Ecosystem.Translation
import AVM.Task.Translation

namespace AVM

def Program.compile {lab : Ecosystem.Label} (eco : Ecosystem lab) (prog : Program lab Unit) : Anoma.Program :=
  let task : Task :=
    Task.absorbParams prog.params fun vals =>
      Program.tasks eco prog vals |>
        Task.compose
  task.toProgram
