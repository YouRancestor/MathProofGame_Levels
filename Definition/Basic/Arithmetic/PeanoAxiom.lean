import Lean
import Std.Data.Nat.Lemmas

notation "ℕ" => Nat

open Nat

/--
0不是任何自然数的后继数。
-/
theorem zero_ne_succ'?' (n : ℕ) : 0 ≠ succ n := (Nat.succ_ne_zero n).symm

/--
不同的自然数有不同的后继数，后继数相同的自然数是同一个数。
-/
theorem succ_inj'?' {a b : ℕ} : succ a = succ b → a = b := Nat.succ_inj'.mp

theorem zero_is_0'?' : zero = 0 := Nat.zero_eq

theorem one_eq_succ_zero'?' : 1 = succ 0 := rfl
