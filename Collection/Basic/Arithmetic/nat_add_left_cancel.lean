import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_zero_add
import Collection.Basic.Arithmetic.nat_succ_add

open Nat
theorem nat_add_left_cancel'?' {t a b : ℕ} : t + a = t + b → a = b := by
  intro h
  induction t
  case zero =>
    rewrite [nat_zero_add'?'] at h
    rewrite [nat_zero_add'?'] at h
    exact h
  case succ n n_ih =>
    apply n_ih
    rewrite [nat_succ_add'?'] at h
    rewrite [nat_succ_add'?'] at h
    have p := nat_succ_inj'?' h
    exact p
