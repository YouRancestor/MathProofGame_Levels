import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

open Nat
theorem nat_add_assoc'?' (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction c
  case zero =>
    rewrite [nat_add_zero'?']
    rewrite [nat_add_zero'?']
    refl
  case succ d hd =>
    rewrite [nat_add_succ'?']
    rewrite [nat_add_succ'?']
    rewrite [nat_add_succ'?']
    rewrite [hd]
    refl
