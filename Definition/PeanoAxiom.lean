import Lean
import Std.Data.Nat.Lemmas

notation "ℕ" => Nat

-- 自然数定义
-- 公理1 0是自然数。
-- 公理2 每个自然数 n 都有一个后继数（successor），记为 succ n 。

open Nat

/--
公理3 0不是任何自然数的后继数。
-/
theorem zero_ne_succ'?' {n : ℕ} : 0 ≠ succ n := (Nat.succ_ne_zero n).symm

/--
公理4 不同的自然数有不同的后继数，后继数相同的自然数是同一个数。
-/
theorem succ_inj'?' {a b : ℕ} : succ a = succ b → a = b := Nat.succ_inj'.mp

-- 公理5 归纳原理（tactic induction）

theorem zero_is_0'?' : zero = 0 := Nat.zero_eq

theorem one_eq_succ_zero'?' : 1 = succ 0 := rfl
