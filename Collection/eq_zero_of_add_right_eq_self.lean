import Definition

import Collection.zero_add
import Collection.succ_add

open Nat

theorem eq_zero_of_add_right_eq_self'?' {a b : ℕ} : a + b = a → b = 0 := by
  intro h
  induction a
  case zero =>
    rewrite [zero_add'?'] at h
    rewrite [zero_is_0'?'] at h
    exact h
  case succ n n_ih =>
    rewrite [succ_add'?'] at h
    have p := succ_inj'?' h
    have q := n_ih p
    exact q
