import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.mul_add
import Collection.Basic.Arithmetic.mul_comm

open Nat in
theorem mul_left_comm'?' (a b c : ℕ) : a * (b * c) = b * (a * c) := by
  induction c
  case zero =>
    rewrite [mul_zero'?']
    rewrite [mul_zero'?']
    rewrite [mul_zero'?']
    refl
  case succ n n_ih =>
    rewrite [mul_succ'?']
    rewrite [mul_succ'?']
    rewrite [mul_add'?']
    rewrite [mul_add'?']
    rewrite [mul_comm'?' b a]
    rewrite [n_ih]
    refl
