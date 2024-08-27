import Definition.Basic.Tutorial.Notation
import Definition.Basic.Tactic

/--
### 讨论（命题）（by_cases）
引入一个命题，对其肯定形式和否定形式分别进行讨论。
#### 提示
x ≠ 1 与 ¬(x = 1) 以及 x = 1 → False 是完全等价的，它们只是同一表达式的不同记法。
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
