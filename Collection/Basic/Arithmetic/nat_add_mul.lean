import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_add_assoc
import Collection.Basic.Arithmetic.nat_add_comm

open Nat
theorem nat_add_mul'?' (a b t : ℕ) : (a + b) * t = a * t + b * t := by
  induction t
  case zero =>
    rewrite [nat_mul_zero'?']
    rewrite [nat_mul_zero'?']
    rewrite [nat_mul_zero'?']
    rewrite [nat_add_zero'?']
    refl
  case succ n n_ih =>
    rewrite [nat_mul_succ'?']
    rewrite [nat_mul_succ'?']
    rewrite [nat_mul_succ'?']
    rewrite [n_ih]
    rewrite [←nat_add_assoc'?']
    rewrite [←nat_add_assoc'?']
    rewrite [nat_add_assoc'?' (a * n) (b * n) a]
    rewrite [nat_add_comm'?' (b * n) a]
    rewrite [←nat_add_assoc'?']
    refl
