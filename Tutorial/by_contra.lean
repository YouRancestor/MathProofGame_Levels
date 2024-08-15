import Tutorial.Notation
import Std.Tactic.Basic

/--
### 反证（by_contra）
**反证**将引入目标的否命题作为一个假设，并将目标转化为False，以便由原目标的否命题与其他已知条件推出矛盾，从而证明原目标的否命题为假，即原目标为真。
-/
example (P Q : Prop) : (¬Q → ¬P) → (P → Q) := by
  intro h
  intro p
  by_contra nq
  refine h ?nq ?p -- 类似 exact _ _
  case nq =>
    exact nq
  case p =>
    exact p
