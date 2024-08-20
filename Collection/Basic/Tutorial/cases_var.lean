import Definition.Basic.Tutorial.Notation
import Definition.Basic.Tactic

open Nat in
/--
### 讨论（cases）
对目标中指定变量的可能取值进行**讨论**，并分别给出证明。例如，对于自然数 n ，根据自然数的定义， n 要么取 0 ，要么取 succ d 。
-/
example (zero_is_0 : zero = 0) (succ_pos : ∀ (n : ℕ), 0 < succ n) : n = 0 ∨ n > 0 := by
  cases n
  case zero =>
    left
    rewrite [zero_is_0]
    refl
  case succ d =>
    right
    exact succ_pos d
