import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_succ_ne_zero

open Nat
theorem nat_add_right_eq_zero'?' {a b : ℕ} : a + b = 0 → a = 0 := by
  intro h
  cases b
  case zero =>
    rewrite [nat_add_zero'?'] at h
    exact h
  case succ n =>
    exfalso
    rewrite [nat_add_succ'?'] at h
    exact nat_succ_ne_zero'?' (a + n) h
