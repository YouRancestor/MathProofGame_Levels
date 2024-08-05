import Tutorial.Notation
import Definition.Tactic

/--
### 自反
当待证明目标形如 x = x（等式） 或 p ↔ p（当且仅当） 时，可以使用战术自反（等价关系的自反性）来完成证明。
-/
example : x + 7 = x + 7 := by
-- 如果要证明的目标为一个等式，且左右两边完全一样，那么就可以使用自反来结束证明。
  refl

example : p ↔ p := by
-- 如果要证明的目标为一个当且仅当式，且左右两边完全一样，那么也可以自反来结束证明。
  refl
