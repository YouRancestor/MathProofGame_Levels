import Definition

open Nat

theorem succ_eq_succ_of_eq'?' {a b : ℕ} : a = b → succ a = succ b := by
  intro h
  rewrite [h]
  refl
