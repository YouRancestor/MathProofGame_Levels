import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.mul_add

open Nat in
theorem mul_assoc'?' (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c
  case zero =>
    rewrite [mul_zero'?']
    rewrite [mul_zero'?']
    rewrite [mul_zero'?']
    refl
  case succ n n_ih =>
    rewrite [mul_succ'?']
    rewrite [mul_succ'?']
    rewrite [mul_add'?']
    rewrite [n_ih]
    refl
