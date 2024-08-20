import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

open Nat in
theorem succ_ne_zero'?' (a : ℕ) : succ a ≠ 0 := by
  intro h
  apply zero_ne_succ'?' a
  symm
  exact h
