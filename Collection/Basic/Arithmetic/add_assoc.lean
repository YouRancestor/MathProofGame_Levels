import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

open Nat
theorem add_assoc'?' (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction c
  case zero =>
    rewrite [add_zero'?']
    rewrite [add_zero'?']
    refl
  case succ d hd =>
    rewrite [add_succ'?']
    rewrite [add_succ'?']
    rewrite [add_succ'?']
    rewrite [hd]
    refl
