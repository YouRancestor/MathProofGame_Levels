import Definition

import Collection.zero_mul
import Collection.succ_mul
import Collection.add_assoc
open Nat

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
