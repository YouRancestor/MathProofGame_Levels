import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

import Collection.Basic.Arithmetic.nat_zero_add

open Nat
theorem nat_mul_one'?' (a : ℕ) : a * 1 = a := by
  rewrite [nat_one_eq_succ_zero'?']
  rewrite [nat_mul_succ'?' a]
  rewrite [nat_mul_zero'?' a]
  rewrite [nat_zero_add'?' a]
  refl
