import Definition.Basic.Tutorial.Notation
import Definition.Basic.Tactic

/--
### （by_cases）
引入一个命题，对其肯定形式和否定形式分别进行讨论。
-/
example (x : ℕ) : x = 1 ∨ x ≠ 1 := by
  let h1 := x = 1 -- 通过点击x=1创建一张卡片
  by_cases h1
  case pos h2 =>
    left
    case h =>
      exact h2
  case neg h2 =>
    right
    case h =>
      exact h2
