import Definition

import Collection.succ_eq_add_one

open Nat

theorem one_mul'?' (a : ℕ) : 1 * a = a := by
  induction a
  case zero =>
    rewrite [mul_zero'?' 1]
    rewrite [zero_is_0'?']
    refl
  case succ n n_ih =>
    rewrite [mul_succ'?' 1 n]
    rewrite [n_ih]
    rewrite [succ_eq_add_one'?']
    refl
