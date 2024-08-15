import Tutorial.Notation
import Tactic.refl

/--
### 自反
当待证明目标形如 x = x（等式的左右两边完全一样） 或 p ↔ p（逻辑等价式的左右两边完全一样） 时，可以使用战术自反（等价关系的自反性）来完成证明。
-/
example : x + 7 = x + 7 := by
  refl

example : p ↔ p := by
  refl
