import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_zero_mul
import Collection.Basic.Arithmetic.nat_succ_mul
import Collection.Basic.Arithmetic.nat_add_assoc

open Nat
theorem nat_mul_add'?' (t a b : Nat) : t * (a + b) = t * a + t * b := by
  induction t
  case zero =>
    rewrite [nat_zero_mul'?']
    rewrite [nat_zero_mul'?']
    rewrite [nat_zero_mul'?']
    rewrite [nat_add_zero'?']
    refl
  case succ n n_ih =>
    rewrite [nat_succ_mul'?']
    rewrite [nat_succ_mul'?']
    rewrite [nat_succ_mul'?']
    rewrite [n_ih]
    rewrite [←nat_add_assoc'?']
    rewrite [←nat_add_assoc'?']
    rewrite [nat_add_assoc'?' (n*a) (n*b) a]
    rewrite [nat_add_comm'?' (n*b) a]
    rewrite [←nat_add_assoc'?']
    refl
