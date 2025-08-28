import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

open Nat
theorem nat_succ_eq_add_one'?' (a : ℕ) : succ a = a + 1 := by
  nth_rewrite 1 [←nat_add_zero'?' a]
  rewrite [nat_add_succ'?']
  refl
