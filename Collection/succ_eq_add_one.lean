import Definition

open Nat

theorem succ_eq_add_one'?' (a : ℕ) : succ a = a + 1 := by
  nth_rewrite 1 [←add_zero'?' a]
  rewrite [add_succ'?']
  refl
