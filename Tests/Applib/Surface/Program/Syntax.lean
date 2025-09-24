import Applib.Surface.Program.Syntax
import Apps.TwoCounter
import Apps.OwnedCounter

namespace TwoCounterApp

open Applib

example (rx ry : Reference Counter) : Program Eco.label Counter := ⟪
  x := fetch rx
  y := fetch ry
  call Counter.Methods.Incr rx (x.count * 2 + y.count)
  call Counter.Methods.Incr ry (y.count * 2 + x.count)
  return {x with count := x.count + y.count}
⟫

def mutualIncrement (rx ry : Reference Counter) (n : Nat) : Program Eco.label Unit := ⟪
  x := fetch rx
  y := fetch ry
  call Counter.Methods.Incr rx (x.count * n + y.count)
  call Counter.Methods.Incr ry (y.count * n + x.count)
  return ()
⟫

def createCounter : Program Eco.label (Reference Counter) := ⟪
  r := create Counter Counter.Constructors.Zero () noSignatures
  call Counter.Methods.Incr r (7 : Nat);
  return r
⟫

example (self : TwoCounter) (n : Nat) : Program Eco.label TwoCounter := ⟪
  invoke mutualIncrement self.c1 self.c2 n
  invoke mutualIncrement self.c2 self.c1 n
  c1 := fetch self.c1
  c2 := fetch self.c2
  if c1.count > c2.count then
    call Counter.Methods.Incr self.c1 (2 : Nat)
  else
    call Counter.Methods.Incr self.c2 (2 : Nat)
  return self
⟫

example (self : TwoCounter) (n : Nat) : Program Eco.label TwoCounter := ⟪
  invoke mutualIncrement self.c1 self.c2 n
  invoke mutualIncrement self.c2 self.c1 n
  c1 := fetch self.c1
  c2 := fetch self.c2
  if c1.count > c2.count then
    call Counter.Methods.Incr self.c1 (2 : Nat)
    call Counter.Methods.Incr self.c2 (1 : Nat)
  else
    call Counter.Methods.Incr self.c2 (2 : Nat)
    invoke mutualIncrement self.c2 self.c1 n
  invoke mutualIncrement self.c1 self.c1 n
  return self
⟫

example (self : TwoCounter) (n : Nat) : Program Eco.label TwoCounter := ⟪
  invoke mutualIncrement self.c1 self.c2 n
  invoke mutualIncrement self.c2 self.c1 n
  c1 := fetch self.c1
  c2 := fetch self.c2
  if c1.count > c2.count then
    call Counter.Methods.Incr self.c1 (2 : Nat)
    call Counter.Methods.Incr self.c2 (1 : Nat)
    invoke mutualIncrement self.c1 self.c1 n
  return self
⟫

example (self : TwoCounter) (n : Nat) : Program Eco.label Counter := ⟪
  invoke mutualIncrement self.c1 self.c2 n
  invoke mutualIncrement self.c2 self.c1 n
  c1 := fetch self.c1
  c2 := fetch self.c2
  if c1.count > c2.count then
    return c1
  else
    return c2
⟫

example : Program Eco.label (Reference TwoCounter) := ⟪
  rx := create Counter Counter.Constructors.Zero () noSignatures
  ry := create Counter Counter.Constructors.Zero () noSignatures
  call Counter.Methods.Incr rx (2 : Nat)
  call Counter.Methods.Incr ry (7 : Nat)
  tc := create TwoCounter TwoCounter.Constructors.Zero (rx, ry) noSignatures
  return tc
⟫

example (self : TwoCounter) (n : Nat) : Program Eco.label TwoCounter := ⟪
  c1 := fetch self.c1
  c2 := fetch self.c2
  call Counter.Methods.Incr self.c1 (c2.count * n + c1.count)
  call Counter.Methods.Incr self.c2 (c1.count * n + c2.count)
  return self
⟫

example (self : TwoCounter) (n : Nat) : Program Eco.label Counter := ⟪
  invoke mutualIncrement self.c1 self.c2 n
  invoke mutualIncrement self.c2 self.c1 n
  cRef := invoke createCounter
  c1 := fetch self.c1
  c2 := fetch self.c2
  match c1.count with
  | 0 => return c2
  | Nat.succ n' =>
    call Counter.Methods.Incr cRef (3 : Nat);
    if c1.count > c2.count then
      c := fetch cRef
      invoke mutualIncrement self.c2 self.c1 (n' + c.count)
      return c1
    else
      invoke mutualIncrement self.c1 self.c2 n'
      return c2
⟫

example (self : TwoCounter) (n : Nat) : Program Eco.label Unit := ⟪
  invoke mutualIncrement self.c1 self.c2 n
  invoke mutualIncrement self.c2 self.c1 n
  c1 := fetch self.c1
  c2 := fetch self.c2
  match c1.count with
  | 0 => return ()
  | Nat.succ n' =>
    if c1.count > c2.count then
      invoke mutualIncrement self.c2 self.c1 n'
    else
      invoke mutualIncrement self.c1 self.c2 n'
    call Counter.Methods.Incr self.c2 n'
  call Counter.Methods.Incr self.c1 n;
  call Counter.Methods.Incr self.c2 n
⟫

example (self : TwoCounter) (n : Nat) : Program Eco.label Counter := ⟪
  invoke mutualIncrement self.c1 self.c2 n
  invoke mutualIncrement self.c2 self.c1 n
  c1 := fetch self.c1
  c2 := fetch self.c2
  match c1.count with
  | 0 => return c2
  | Nat.succ n' =>
    if c1.count > c2.count then
      invoke mutualIncrement self.c2 self.c1 n'
      return c1
    else
      if c1.count < c2.count then
        invoke mutualIncrement self.c1 self.c2 n'
        return c2
      else
        return c1
⟫

example (self : TwoCounter) (n : Nat) : Program Eco.label Counter := ⟪
  invoke mutualIncrement self.c1 self.c2 n
  invoke mutualIncrement self.c2 self.c1 n
  c1 := fetch self.c1
  c2 := fetch self.c2
  !let x := c1.count + c2.count
  match c1.count with
  | 0 => ⟪return c2⟫
  | Nat.succ n' =>
    if c1.count > c2.count then ⟪
      invoke mutualIncrement self.c2 self.c1 (n' + x)
      return c1
    ⟫ else ⟪
      if c1.count < c2.count then
        invoke mutualIncrement self.c1 self.c2 (n' + x)
        return c2
      else
        return c1
    ⟫
⟫

example (self : TwoCounter) (n : Nat) : Program Eco.label Counter := ⟪
  invoke mutualIncrement self.c1 self.c2 n
  invoke mutualIncrement self.c2 self.c1 n
  c1 := fetch self.c1
  c2 := fetch self.c2
  let x : Nat := c1.count + c2.count
  match c1.count with
  | 0 => return c2
  | Nat.succ n' =>
    if c1.count > c2.count then
      invoke mutualIncrement self.c2 self.c1 (n' + x)
      return c1
    else
      if c1.count < c2.count then
        invoke mutualIncrement self.c1 self.c2 (n' + x)
        return c2
      else
        return c1
⟫

example (self : TwoCounter) (n : Nat) : Program Eco.label Counter := ⟪
  invoke mutualIncrement self.c1 self.c2 n
  invoke mutualIncrement self.c2 self.c1 n
  c1 := fetch self.c1
  c2 := fetch self.c2
  match c1.count with
  | 0 => return c2
  | Nat.succ n' =>
    if c1.count >= c2.count then
      invoke mutualIncrement self.c2 self.c1 n'
      if c1.count == c2.count then
        invoke mutualIncrement self.c1 self.c2 n'
      else
        invoke mutualIncrement self.c2 self.c1 n'
    upgrade self.c1 to c2
    return c1
⟫

end TwoCounterApp

namespace OwnedCounter

open Applib

example (r : Reference OwnedCounter) (newOwner : PublicKey) : Program label (Reference OwnedCounter) := ⟪
  c := fetch r
  call OwnedCounter.Methods.Transfer r newOwner;
  r' := create OwnedCounter OwnedCounter.Constructors.Zero () noSignatures
  call OwnedCounter.Methods.Incr r' (c.count + 1);
  destroy OwnedCounter.Destructors.Ten r () noSignatures
  return r'
⟫

example (n : Nat) : Program label (Reference OwnedCounter) := ⟪
  r := create OwnedCounter OwnedCounter.Constructors.Zero () noSignatures
  call OwnedCounter.Methods.Incr r n;
  create OwnedCounter OwnedCounter.Constructors.Zero () noSignatures
  create OwnedCounter OwnedCounter.Constructors.Zero () noSignatures
  return r
⟫

end OwnedCounter
