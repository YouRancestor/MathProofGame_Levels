import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

open Nat
theorem nat_zero_add'?' (a : ℕ) : 0 + a = a := by
  induction a
  case zero =>
    rewrite [nat_zero_is_0'?']
    rewrite [nat_add_zero'?']
    refl
  case succ a ih =>
    rewrite [nat_add_succ'?']
    rewrite [ih]
    refl
