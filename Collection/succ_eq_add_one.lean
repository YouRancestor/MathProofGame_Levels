import Definition

import Collection.zero_add
import Collection.succ_add

open Nat

theorem succ_eq_add_one'?' (a : ℕ) : succ a = a + 1 := by
  induction a
  case zero =>
    rewrite [zero_add'?']
    rewrite [one_eq_succ_zero'?']
    rewrite [zero_is_0'?']
    refl
  case succ n n_ih =>
    nth_rewrite 1 [n_ih]
    rewrite [succ_add'?']
    refl
