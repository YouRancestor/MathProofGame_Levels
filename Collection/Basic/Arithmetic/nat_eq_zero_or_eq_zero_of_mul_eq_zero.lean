import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_succ_mul
import Collection.Basic.Arithmetic.nat_add_left_eq_zero

open Nat
theorem nat_eq_zero_or_eq_zero_of_mul_eq_zero'?' {a b : ℕ} : a * b = 0 → a = 0 ∨ b = 0 := by
  intro h
  cases a
  case zero =>
    left
    rewrite [nat_zero_is_0'?']
    refl
  case succ n =>
    right
    rewrite [nat_succ_mul'?'] at h
    exact nat_add_left_eq_zero'?' h
