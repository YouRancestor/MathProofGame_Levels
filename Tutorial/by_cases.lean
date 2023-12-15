import Tutorial.Notation
import Definition.Tactic

/--
### （by_cases）
引入一个命题，对其肯定形式和否定形式分别进行讨论。
-/
example (x : ℕ) : x = 1 ∨ x ≠ 1 := by
  let h := x = 1
  by_cases h
  case pos h' =>
    left
    exact h'
  case neg h' =>
    right
    exact h'
