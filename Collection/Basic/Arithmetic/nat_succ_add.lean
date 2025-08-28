import Definition.Basic.Arithmetic
import Definition.Basic.Tactic

open Nat
theorem nat_succ_add'?' (a b : ℕ) : succ a + b = succ (a + b) := by
  induction b
  case zero =>
    -- rewrite [nat_zero_is_0'?']
    rewrite [nat_add_zero'?' a]
    rewrite [nat_add_zero'?' (succ a)]
    refl
  case succ d hd =>
    rewrite [nat_add_succ'?']
    rewrite [nat_add_succ'?']
    rewrite [hd]
    refl
