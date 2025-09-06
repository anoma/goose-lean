import AVM.Class.Member
import AVM.Class.Label
import AVM.Ecosystem.Label

structure FunctionData : Type where
  numConstructed : Nat
  numDestroyed : Nat
  numSelvesDestroyed : Nat
