import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.succ_ne_zero

open Nat
theorem add_right_eq_zero'?' {a b : ℕ} : a + b = 0 → a = 0 := by
  intro h
  cases b
  case zero =>
    rewrite [add_zero'?'] at h
    exact h
  case succ n =>
    exfalso
    rewrite [add_succ'?'] at h
    exact succ_ne_zero'?' (a + n) h
