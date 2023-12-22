import Definition

import Collection.succ_eq_add_one
import Collection.succ_add

open Nat

theorem add_right_comm'?' (a b c : ℕ) : a + b + c = a + c + b := by
  induction c
  case zero =>
    rewrite [add_zero'?']
    rewrite [add_zero'?']
    refl
  case succ n n_ih =>
    rewrite [add_succ'?']
    rewrite [add_succ'?']
    rewrite [succ_add'?']
    rewrite [n_ih]
    refl
