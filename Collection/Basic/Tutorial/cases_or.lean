import Definition.Basic.Tactic

/--
### 逻辑或（cases）
对于已知条件中的或型命题 P ∨ Q ，**讨论**可以将其拆分成两种情况，并在其中一种情况中引入 P 作为假设，另一种情况中引入 Q 。
-/
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h
  case inl p =>
    right
    exact p
  case inr q =>
    left
    exact q
