import Definition

open Nat

theorem zero_mul'?' (a : ℕ) : 0 * a = 0 := by
  induction a
  case zero =>
    rewrite [mul_zero'?']
    refl
  case succ n n_ih =>
    rewrite [mul_succ'?']
    rewrite [add_zero'?']
    rewrite [n_ih]
    refl
