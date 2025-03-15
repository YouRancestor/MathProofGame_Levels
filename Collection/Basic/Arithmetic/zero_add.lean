import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

open Nat
theorem zero_add'?' (a : ℕ) : 0 + a = a := by
  induction a
  case zero =>
    rewrite [zero_is_0'?']
    rewrite [add_zero'?']
    refl
  case succ a ih =>
    rewrite [add_succ'?']
    rewrite [ih]
    refl
