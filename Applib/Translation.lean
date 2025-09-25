import Applib.Surface.Program
import AVM.Authorization

namespace Applib

def Program.compile {lab : AVM.Scope.Label} (scope : AVM.Scope lab) (prog : Program lab PUnit) : Anoma.Program :=
  prog.toAVM |> AVM.Program.compile scope

end Applib
