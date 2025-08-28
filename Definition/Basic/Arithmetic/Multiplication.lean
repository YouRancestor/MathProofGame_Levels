import Definition.Basic.Arithmetic.PeanoAxiom
import Definition.Basic.Arithmetic.Addition

open Nat

/--
任何自然数乘0等于0
-/
theorem nat_mul_zero'?' (n : ℕ) : n * 0 = 0 := by rfl

/--
乘上一个数的后继数等于乘上那个数再加上自身
-/
theorem nat_mul_succ'?' (n m : ℕ) : n * (succ m) = n * m + n := Nat.mul_succ _ _
