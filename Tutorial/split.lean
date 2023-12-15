import Tutorial.Notation
import Definition.Tactic

example : if n = 0 then n >= 0 else n ≠ 0 := by
  split
  case inl h =>
    simp
  case inr h =>
    exact h
