import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_mul_add

open Nat
theorem nat_mul_assoc'?' (a b c : Nat) : (a * b) * c = a * (b * c) := by
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
    rewrite [n_ih]
    refl
