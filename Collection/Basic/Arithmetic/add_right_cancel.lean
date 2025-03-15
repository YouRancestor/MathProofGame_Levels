import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

open Nat
theorem add_right_cancel'?' {t a b : ℕ} : a + t = b + t → a = b := by
  intro h
  induction t
  case zero =>
    rewrite [add_zero'?'] at h
    rewrite [add_zero'?'] at h
    exact h
  case succ n n_ih =>
    rewrite [add_succ'?'] at h
    rewrite [add_succ'?'] at h
    apply n_ih
    have p := succ_inj'?' h
    exact p
