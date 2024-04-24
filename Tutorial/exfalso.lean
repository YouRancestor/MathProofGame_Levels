import Tutorial.Notation
import Definition.Tactic

/--
### 证伪（exfalso）
相互矛盾的前提可以推导出一切命题。若已知条件中存在矛盾，可以使用**证伪**将目标转化为False，以便用现有条件推出矛盾（False）。
-/
example (P Q : Prop) : (P ∧ ¬P) → Q := by
  -- 用矛盾的 P 和 ¬P 可以推出任意命题 Q
  intro h
  cases h
  case intro h_left h_right =>
    exfalso
    case h =>
      apply h_right
      exact h_left
