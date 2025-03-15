import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.zero_mul
import Collection.Basic.Arithmetic.succ_mul

open Nat
theorem mul_comm'?' (a b : ℕ) : a * b = b * a := by
  induction b
  case zero =>
    rewrite [mul_zero'?']
    rewrite [zero_mul'?']
    refl
  case succ n n_ih =>
    rewrite [mul_succ'?']
    rewrite [succ_mul'?']
    rewrite [n_ih]
    refl
