import Definition.PeanoAxiom

open Nat

-- 加法定义

/--
任何自然数加0等于它本身
-/
theorem add_zero {n : ℕ} : n + 0 = n := Nat.add_zero _

/--
加上一个数的后继数等于加上那个数的结果的后继
-/
theorem add_succ {n m : ℕ} : n + (succ m) = succ (n + m) := Nat.add_succ _ _
