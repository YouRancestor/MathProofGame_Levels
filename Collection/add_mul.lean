import Definition

import Collection.add_assoc
import Collection.add_comm

open Nat

theorem add_mul'?' (a b t : ℕ) : (a + b) * t = a * t + b * t := by
  induction t
  case zero =>
    rewrite [mul_zero'?']
    rewrite [mul_zero'?']
    rewrite [mul_zero'?']
    rewrite [add_zero'?']
    refl
  case succ n n_ih =>
    rewrite [mul_succ'?']
    rewrite [mul_succ'?']
    rewrite [mul_succ'?']
    rewrite [n_ih]
    rewrite [←add_assoc'?']
    rewrite [←add_assoc'?']
    rewrite [add_assoc'?' (a * n) (b * n) a]
    rewrite [add_comm'?' (b * n) a]
    rewrite [←add_assoc'?']
    refl
