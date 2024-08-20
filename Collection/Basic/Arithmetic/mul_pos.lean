import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.succ_mul
import Collection.Basic.Arithmetic.add_left_eq_zero

open Nat in
theorem mul_pos'?' {a b : ℕ} : a ≠ 0 ∧ b ≠ 0 → a * b ≠ 0 := by
  intro h
  intro h1
  cases h
  case intro left right =>
    cases a
    case zero =>
      apply left
      rewrite [zero_is_0'?']
      refl
    case succ n =>
      apply right
      rewrite [succ_mul'?'] at h1
      have p := add_left_eq_zero'?' h1
      exact p
