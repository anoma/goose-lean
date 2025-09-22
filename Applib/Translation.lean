import Applib.Surface.Program
import AVM.Authorization

namespace Applib

def Program.compile {lab : AVM.Ecosystem.Label} (eco : AVM.Ecosystem lab) (prog : Program lab PUnit) : Anoma.Program :=
  prog.toAVM |> AVM.Program.compile eco

end Applib
