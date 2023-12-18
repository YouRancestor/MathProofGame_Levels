import Definition

import Collection.zero_add
import Collection.succ_add

open Nat

theorem add_comm'?' (a b : ℕ) : a + b = b + a := by
  induction b
  case zero =>
    rewrite [add_zero'?']
    rewrite [zero_add'?']
    refl
  case succ n n_ih =>
    rewrite [add_succ'?']
    rewrite [succ_add'?']
    rewrite [n_ih]
    refl
