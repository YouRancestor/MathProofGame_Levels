import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.zero_mul
import Collection.Basic.Arithmetic.succ_mul
import Collection.Basic.Arithmetic.add_assoc

open Nat in
theorem mul_add'?' (t a b : Nat) : t * (a + b) = t * a + t * b := by
  induction t
  case zero =>
    rewrite [zero_mul'?']
    rewrite [zero_mul'?']
    rewrite [zero_mul'?']
    rewrite [add_zero'?']
    refl
  case succ n n_ih =>
    rewrite [succ_mul'?']
    rewrite [succ_mul'?']
    rewrite [succ_mul'?']
    rewrite [n_ih]
    rewrite [←add_assoc'?']
    rewrite [←add_assoc'?']
    rewrite [add_assoc'?' (n*a) (n*b) a]
    rewrite [add_comm'?' (n*b) a]
    rewrite [←add_assoc'?']
    refl
