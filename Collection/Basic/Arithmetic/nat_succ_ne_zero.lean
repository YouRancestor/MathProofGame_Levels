import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

open Nat
theorem nat_succ_ne_zero'?' (a : ℕ) : succ a ≠ 0 := by
  intro h
  apply nat_zero_ne_succ'?' a
  symm
  exact h
