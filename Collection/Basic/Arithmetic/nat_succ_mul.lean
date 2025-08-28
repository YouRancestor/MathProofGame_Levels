import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_add_assoc
import Collection.Basic.Arithmetic.nat_add_comm

open Nat
theorem nat_succ_mul'?' (a b : ℕ) : succ a * b = a * b + b := by
  induction b
  case zero =>
    rewrite [nat_mul_zero'?' (succ a)]
    rewrite [nat_mul_zero'?' a]
    rewrite [nat_add_zero'?' 0]
    refl
  case succ n n_ih =>
    rewrite [nat_mul_succ'?' (succ a) n]
    rewrite [nat_mul_succ'?' a n]
    rewrite [n_ih]
    rewrite [nat_add_succ'?']
    rewrite [nat_add_succ'?']
    rewrite [nat_add_assoc'?' (a * n) n a]
    rewrite [nat_add_comm'?' n a]
    rewrite [←nat_add_assoc'?' (a * n) a n]
    refl
