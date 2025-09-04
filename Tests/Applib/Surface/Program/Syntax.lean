import Applib.Surface.Program.Syntax
import Apps.TwoCounter
import Apps.OwnedCounter

namespace TwoCounterApp

open Applib

example (rx ry : Reference Counter) : Program Eco.lab Counter := ⟪
  x := fetch rx
  y := fetch ry
  call Counter.Methods.Incr rx (x.count * 2 + y.count)
  call Counter.Methods.Incr ry (y.count * 2 + x.count)
  return {x with count := x.count + y.count}
⟫

def mutualIncrement (rx ry : Reference Counter) (n : Nat) : Program Eco.lab Unit := ⟪
  x := fetch rx
  y := fetch ry
  call Counter.Methods.Incr rx (x.count * n + y.count)
  call Counter.Methods.Incr ry (y.count * n + x.count)
  return ()
⟫

example (self : TwoCounter) (n : Nat) : Program Eco.lab TwoCounter := ⟪
  invoke mutualIncrement self.c1 self.c2 n
  invoke mutualIncrement self.c2 self.c1 n
  return self
⟫

example : Program Eco.lab (Reference TwoCounter) := ⟪
  rx := create Counter Counter.Constructors.Zero ()
  ry := create Counter Counter.Constructors.Zero ()
  call Counter.Methods.Incr rx (2 : Nat)
  call Counter.Methods.Incr ry (7 : Nat)
  tc := create TwoCounter TwoCounter.Constructors.Zero (rx, ry)
  return tc
⟫

example (self : TwoCounter) (n : Nat) : Program Eco.lab TwoCounter := ⟪
  c1 := fetch self.c1
  c2 := fetch self.c2
  call Counter.Methods.Incr self.c1 (c2.count * n + c1.count)
  call Counter.Methods.Incr self.c2 (c1.count * n + c2.count)
  return self
⟫

end TwoCounterApp

namespace OwnedCounter

open Applib

example (r : Reference OwnedCounter) (newOwner : PublicKey) : Program label (Reference OwnedCounter) := ⟪
  c := fetch r
  call OwnedCounter.Methods.Transfer r newOwner
  r' := create OwnedCounter OwnedCounter.Constructors.Zero ()
  call OwnedCounter.Methods.Incr r' (c.count + 1)
  destroy OwnedCounter.Destructors.Ten r ()
  return r'
⟫

example (n : Nat) : Program label (Reference OwnedCounter) := ⟪
  r := create OwnedCounter OwnedCounter.Constructors.Zero ()
  call OwnedCounter.Methods.Incr r n
  create OwnedCounter OwnedCounter.Constructors.Zero ()
  create OwnedCounter OwnedCounter.Constructors.Zero ()
  return r
⟫

end OwnedCounter
