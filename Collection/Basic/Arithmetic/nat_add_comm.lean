import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_zero_add
import Collection.Basic.Arithmetic.nat_succ_add

open Nat
theorem nat_add_comm'?' (a b : ℕ) : a + b = b + a := by
  induction b
  case zero =>
    rewrite [nat_add_zero'?']
    rewrite [nat_zero_add'?']
    refl
  case succ n n_ih =>
    rewrite [nat_add_succ'?']
    rewrite [nat_succ_add'?']
    rewrite [n_ih]
    refl
