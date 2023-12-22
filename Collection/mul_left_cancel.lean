import Definition

import Collection.mul_eq_zero_iff
import Collection.add_left_eq_zero
import Collection.add_right_cancel
import Collection.succ_eq_succ_of_eq

open Nat

theorem mul_left_cancel'?' {t a b : ℕ} {ht : t ≠ 0} : t * a = t * b → a = b := by
  intro h
  induction b generalizing a
  case zero =>
    rewrite [mul_zero'?'] at h
    have p := mul_eq_zero_iff'?'.mp h
    cases p
    case inl ht' =>
      exfalso
      apply ht
      exact ht'
    case inr ht' =>
      exact ht'
  case succ n n_ih =>
    cases a
    case zero =>
      rewrite [mul_zero'?'] at h
      rewrite [mul_succ'?'] at h
      symm at h
      have p := add_left_eq_zero'?' h
      exfalso
      apply ht
      exact p
    case succ d =>
      rewrite [mul_succ'?'] at h
      rewrite [mul_succ'?'] at h
      have p := add_right_cancel'?' h
      have q := n_ih p
      rewrite [←q]
      apply succ_eq_succ_of_eq'?'
      refl
