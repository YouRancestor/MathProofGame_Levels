import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

open Nat
theorem nat_add_right_cancel'?' {t a b : ℕ} : a + t = b + t → a = b := by
  intro h
  induction t
  case zero =>
    rewrite [nat_add_zero'?'] at h
    rewrite [nat_add_zero'?'] at h
    exact h
  case succ n n_ih =>
    rewrite [nat_add_succ'?'] at h
    rewrite [nat_add_succ'?'] at h
    apply n_ih
    have p := nat_succ_inj'?' h
    exact p
