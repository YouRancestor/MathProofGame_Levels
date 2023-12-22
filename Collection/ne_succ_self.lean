import Definition

import Collection.add_left_cancel

open Nat

theorem ne_succ_self'?' {a : ℕ} : a ≠ succ a := by
  cases a
  case zero =>
    exact zero_ne_succ'?'
  case succ n =>
    intro h
    have p := succ_inj'?' h
    nth_rewrite 1 [←add_zero'?' n] at p
    have q := add_left_cancel'?' p
    exact zero_ne_succ'?' q

theorem ne_succ_self (a : ℕ) : a ≠ succ a := by
  intro h
  show_term cases h
