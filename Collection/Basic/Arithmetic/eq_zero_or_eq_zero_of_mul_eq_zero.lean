import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.succ_mul
import Collection.Basic.Arithmetic.add_left_eq_zero

open Nat in
theorem eq_zero_or_eq_zero_of_mul_eq_zero'?' {a b : ℕ} : a * b = 0 → a = 0 ∨ b = 0 := by
  intro h
  cases a
  case zero =>
    left
    rewrite [zero_is_0'?']
    refl
  case succ n =>
    right
    rewrite [succ_mul'?'] at h
    exact add_left_eq_zero'?' h
