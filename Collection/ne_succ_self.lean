import Definition

import Collection.add_left_cancel
-- import Collection.succ_eq_add_one

open Nat

theorem ne_succ_self'?' {a : ℕ} : a ≠ succ a := by
  cases a
  case zero =>
    exact zero_ne_succ'?' zero
  case succ n =>
    intro h
    have p := succ_inj'?' h
    nth_rewrite 1 [←add_zero'?' n] at p
    have q := add_left_cancel'?' p
    -- rewrite [←zero_add'?' 1] at q
    -- rewrite [←succ_eq_add_one'?'] at q
    exact zero_ne_succ'?' 0 q

theorem ne_succ_self (a : ℕ) : a ≠ succ a := by
  intro h
  show_term cases h
