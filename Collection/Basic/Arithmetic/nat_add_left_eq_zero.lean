import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_zero_add
import Collection.Basic.Arithmetic.nat_succ_add
import Collection.Basic.Arithmetic.nat_succ_ne_zero

open Nat
theorem nat_add_left_eq_zero'?' {a b : ℕ} : a + b = 0 → b = 0 := by
  intro h
  cases a
  case zero =>
    rewrite [nat_zero_add'?'] at h
    exact h
  case succ n =>
    exfalso
    rewrite [nat_succ_add'?'] at h
    exact nat_succ_ne_zero'?' (n + b) h
