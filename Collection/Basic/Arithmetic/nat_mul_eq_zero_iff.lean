import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_succ_mul
import Collection.Basic.Arithmetic.nat_add_left_eq_zero
import Collection.Basic.Arithmetic.nat_zero_mul

open Nat
theorem nat_mul_eq_zero_iff'?' {a b : ℕ} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  case mp =>
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
  case mpr =>
    intro h
    cases h
    case inl ha =>
      rewrite [ha]
      exact nat_zero_mul'?' b
    case inr hb =>
      rewrite [hb]
      exact nat_mul_zero'?' a
