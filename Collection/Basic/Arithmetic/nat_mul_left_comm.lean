import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_mul_add
import Collection.Basic.Arithmetic.nat_mul_comm

open Nat
theorem nat_mul_left_comm'?' (a b c : ℕ) : a * (b * c) = b * (a * c) := by
  induction c
  case zero =>
    rewrite [nat_mul_zero'?']
    rewrite [nat_mul_zero'?']
    rewrite [nat_mul_zero'?']
    refl
  case succ n n_ih =>
    rewrite [nat_mul_succ'?']
    rewrite [nat_mul_succ'?']
    rewrite [nat_mul_add'?']
    rewrite [nat_mul_add'?']
    rewrite [nat_mul_comm'?' b a]
    rewrite [n_ih]
    refl
