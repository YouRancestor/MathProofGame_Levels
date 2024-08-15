import Tutorial.Notation
import Tactic.right

open Nat in
/--
### 左/右（left/right）
对于或型目标 P ∨ Q ，只需证明 P、Q 其一即可。使用“左”选择 P ，“右”选择 Q ，然后进行证明。
-/
example (P Q : Prop) : Q → P ∨ Q := by
  intro q
  right
  case h =>
    exact q
