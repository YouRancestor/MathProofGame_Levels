import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_add_left_cancel

open Nat
theorem nat_ne_succ_self'?' {a : ℕ} : a ≠ succ a := by
  cases a
  case zero =>
    exact nat_zero_ne_succ'?' zero
  case succ n =>
    intro h
    have p := nat_succ_inj'?' h
    nth_rewrite 1 [←nat_add_zero'?' n] at p
    have q := nat_add_left_cancel'?' p
    -- rewrite [←nat_zero_add'?' 1] at q
    -- rewrite [←nat_succ_eq_add_one'?'] at q
    exact nat_zero_ne_succ'?' 0 q

open Nat
theorem nat_ne_succ_self (a : ℕ) : a ≠ succ a := by
  intro h
  show_term cases h
