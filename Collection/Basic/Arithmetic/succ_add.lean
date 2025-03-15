import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

open Nat
theorem succ_add'?' (a b : ℕ) : succ a + b = succ (a + b) := by
  induction b
  case zero =>
    -- rewrite [zero_is_0'?']
    rewrite [add_zero'?' a]
    rewrite [add_zero'?' (succ a)]
    refl
  case succ d hd =>
    rewrite [add_succ'?']
    rewrite [add_succ'?']
    rewrite [hd]
    refl
