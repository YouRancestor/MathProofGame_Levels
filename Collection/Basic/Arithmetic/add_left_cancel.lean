import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.zero_add
import Collection.Basic.Arithmetic.succ_add

open Nat
theorem add_left_cancel'?' {t a b : ℕ} : t + a = t + b → a = b := by
  intro h
  induction t
  case zero =>
    rewrite [zero_add'?'] at h
    rewrite [zero_add'?'] at h
    exact h
  case succ n n_ih =>
    apply n_ih
    rewrite [succ_add'?'] at h
    rewrite [succ_add'?'] at h
    have p := succ_inj'?' h
    exact p
