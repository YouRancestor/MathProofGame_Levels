import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_succ_eq_add_one

open Nat
theorem nat_one_mul'?' (a : ℕ) : 1 * a = a := by
  induction a
  case zero =>
    rewrite [nat_mul_zero'?' 1]
    rewrite [nat_zero_is_0'?']
    refl
  case succ n n_ih =>
    rewrite [nat_mul_succ'?' 1 n]
    rewrite [n_ih]
    rewrite [nat_succ_eq_add_one'?']
    refl
