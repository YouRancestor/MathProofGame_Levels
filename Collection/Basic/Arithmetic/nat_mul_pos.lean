import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_succ_mul
import Collection.Basic.Arithmetic.nat_add_left_eq_zero

open Nat
theorem nat_mul_pos'?' {a b : ℕ} : a ≠ 0 ∧ b ≠ 0 → a * b ≠ 0 := by
  intro h
  intro h1
  cases h
  case intro left right =>
    cases a
    case zero =>
      apply left
      rewrite [nat_zero_is_0'?']
      refl
    case succ n =>
      apply right
      rewrite [nat_succ_mul'?'] at h1
      have p := nat_add_left_eq_zero'?' h1
      exact p
