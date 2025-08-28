import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

open Nat
theorem nat_zero_mul'?' (a : ℕ) : 0 * a = 0 := by
  induction a
  case zero =>
    rewrite [nat_mul_zero'?']
    refl
  case succ n n_ih =>
    rewrite [nat_mul_succ'?']
    rewrite [nat_add_zero'?']
    rewrite [n_ih]
    refl
