import Applib.Surface.Program.Syntax
import Apps.TwoCounter

open Applib
open TwoCounterApp

-- set_option trace.Elab.step true

/-
def Counter.prog0 : Program Eco.lab Counter :=
Program.fetch  (  fun  _  => counterRef
   )  <|
 Program.fetch  (  fun  ⟨ x  ,  _  ⟩  => counterRef
   )  <|
 Program.call Counter Counter.Methods.Incr  (  fun  ⟨ x  ,  ⟨ y  ,  _  ⟩  ⟩  => counterRef  ) (  fun  ⟨ x  ,  ⟨ y  ,  _  ⟩  ⟩  => (x.count + y.count))
   <|
 Program.return  (  fun  ⟨ x  ,  ⟨ y  ,  _  ⟩  ⟩  => {x with count := x.count + y.count}
 )
-/

def Counter.prog1 (rx ry : Reference Counter) : Program Eco.lab Counter := ⟪
  x := fetch rx
  y := fetch ry
  call Counter Counter.Methods.Incr rx (x.count * 2 + y.count)
  call Counter Counter.Methods.Incr ry (y.count * 2 + x.count)
  return {x with count := x.count + y.count}
⟫

def Counter.prog2 (rx ry : Reference Counter) : Program Eco.lab Unit := ⟪
  x := fetch rx
  y := fetch ry
  call Counter Counter.Methods.Incr rx (x.count * 2 + y.count)
  call Counter Counter.Methods.Incr ry (y.count * 2 + x.count)
  return ()
⟫
