import Tutorial.Notation
import Definition.Tactic
/--
### 逻辑与（cases）
对于已知条件中的且型命题 P ∧ Q ，也可以使用**讨论**，但 P 和 Q 需要同时为真，即同时引入 P 和 Q 作为假设，因此只需要讨论这一种情况。
-/
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  cases h
  case intro p q =>
    constructor
    case left =>
      exact q
    case right =>
      exact p
