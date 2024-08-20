import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.zero_add
import Collection.Basic.Arithmetic.succ_add
import Collection.Basic.Arithmetic.succ_ne_zero

open Nat in
theorem add_left_eq_zero'?' {a b : ℕ} : a + b = 0 → b = 0 := by
  intro h
  cases a
  case zero =>
    rewrite [zero_add'?'] at h
    exact h
  case succ n =>
    exfalso
    rewrite [succ_add'?'] at h
    exact succ_ne_zero'?' (n + b) h
