import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_mul_eq_zero_iff
import Collection.Basic.Arithmetic.nat_add_left_eq_zero
import Collection.Basic.Arithmetic.nat_add_right_cancel
import Collection.Basic.Arithmetic.nat_succ_eq_succ_of_eq

open Nat
theorem nat_mul_left_cancel'?' {t a b : ℕ} {ht : t ≠ 0} : t * a = t * b → a = b := by
  intro h
  induction b generalizing a
  case zero =>
    rewrite [nat_mul_zero'?'] at h
    have p := nat_mul_eq_zero_iff'?'.mp h
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
      rewrite [nat_mul_zero'?'] at h
      rewrite [nat_mul_succ'?'] at h
      symm at h
      have p := nat_add_left_eq_zero'?' h
      exfalso
      apply ht
      exact p
    case succ d =>
      rewrite [nat_mul_succ'?'] at h
      rewrite [nat_mul_succ'?'] at h
      have p := nat_add_right_cancel'?' h
      have q := n_ih p
      rewrite [←q]
      apply nat_succ_eq_succ_of_eq'?'
      refl
