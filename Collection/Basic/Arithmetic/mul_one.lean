import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.zero_add

open Nat
theorem mul_one (a : ℕ) : a * 1 = a := by
  rewrite [one_eq_succ_zero'?']
  rewrite [mul_succ'?' a]
  rewrite [mul_zero'?' a]
  rewrite [zero_add'?' a]
  refl
