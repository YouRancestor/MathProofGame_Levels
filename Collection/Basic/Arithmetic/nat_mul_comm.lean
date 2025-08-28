import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_zero_mul
import Collection.Basic.Arithmetic.nat_succ_mul

open Nat
theorem nat_mul_comm'?' (a b : ℕ) : a * b = b * a := by
  induction b
  case zero =>
    rewrite [nat_mul_zero'?']
    rewrite [nat_zero_mul'?']
    refl
  case succ n n_ih =>
    rewrite [nat_mul_succ'?']
    rewrite [nat_succ_mul'?']
    rewrite [n_ih]
    refl
