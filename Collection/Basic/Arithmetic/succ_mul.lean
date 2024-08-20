import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.add_assoc
import Collection.Basic.Arithmetic.add_comm

open Nat in
theorem succ_mul'?' (a b : ℕ) : succ a * b = a * b + b := by
  induction b
  case zero =>
    rewrite [mul_zero'?' (succ a)]
    rewrite [mul_zero'?' a]
    rewrite [add_zero'?' 0]
    refl
  case succ n n_ih =>
    rewrite [mul_succ'?' (succ a) n]
    rewrite [mul_succ'?' a n]
    rewrite [n_ih]
    rewrite [add_succ'?']
    rewrite [add_succ'?']
    rewrite [add_assoc'?' (a * n) n a]
    rewrite [add_comm'?' n a]
    rewrite [←add_assoc'?' (a * n) a n]
    refl
