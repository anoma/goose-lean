import AVM

namespace Applib

open AVM

def Program (lab : Ecosystem.Label) (Result : Type) := Class.Member.Body lab Result .empty

def Program.map {lab : Ecosystem.Label} {A B : Type} (f : A → B) (prog : Program lab A) : Program lab B := Class.Member.Body.map f prog

alias Program.create := Class.Member.Body.constructor
alias Program.destroy := Class.Member.Body.destructor
alias Program.call := Class.Member.Body.method
alias Program.fetch := Class.Member.Body.fetch
alias Program.return := Class.Member.Body.return

end Applib
