import Definition

open Nat

theorem succ_ne_zero'?' (a : ℕ) : succ a ≠ 0 := by
  intro h
  symm at h
  exact zero_ne_succ'?' h
