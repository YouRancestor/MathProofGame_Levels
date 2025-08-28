import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_zero_add
import Collection.Basic.Arithmetic.nat_succ_add

open Nat
theorem nat_eq_zero_of_add_right_eq_self'?' {a b : ℕ} : a + b = a → b = 0 := by
  intro h
  induction a
  case zero =>
    rewrite [nat_zero_add'?'] at h
    rewrite [nat_zero_is_0'?'] at h
    exact h
  case succ n n_ih =>
    rewrite [nat_succ_add'?'] at h
    have p := nat_succ_inj'?' h
    have q := n_ih p
    exact q
