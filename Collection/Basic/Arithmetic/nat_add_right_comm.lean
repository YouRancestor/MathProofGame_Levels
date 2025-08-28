import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_succ_eq_add_one
import Collection.Basic.Arithmetic.nat_succ_add

open Nat
theorem nat_add_right_comm'?' (a b c : ℕ) : a + b + c = a + c + b := by
  induction c
  case zero =>
    rewrite [nat_add_zero'?']
    rewrite [nat_add_zero'?']
    refl
  case succ n n_ih =>
    rewrite [nat_add_succ'?']
    rewrite [nat_add_succ'?']
    rewrite [nat_succ_add'?']
    rewrite [n_ih]
    refl
