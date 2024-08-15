import Tutorial.Notation
import Tactic.refl

/--
### 代换（反向）
假设我们有一个已知条件 a = b，那么由等价关系的对称性，我们不仅可以使用代换来将目标中出现的 a 替换为 b，也可以将目标中出现的 b 替换为 a 。
-/
example (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  -- 使用代换将目标改写为 2 * y = 2 * y
  rewrite [←h]
  refl
