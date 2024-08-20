import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.succ_mul
import Collection.Basic.Arithmetic.add_left_eq_zero
import Collection.Basic.Arithmetic.zero_mul

open Nat in
theorem mul_eq_zero_iff'?' {a b : ℕ} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  case mp =>
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
  case mpr =>
    intro h
    cases h
    case inl ha =>
      rewrite [ha]
      exact zero_mul'?' b
    case inr hb =>
      rewrite [hb]
      exact mul_zero'?' a
