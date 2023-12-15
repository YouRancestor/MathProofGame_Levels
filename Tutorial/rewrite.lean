import Tutorial.Notation
import Definition.Tactic

/--
### 代换（rewrite）
假设我们有一个已知条件 a = b，那么我们就可以使用代换来将目标或其他已知条件中出现的 a 替换为 b ，从而对目标或假设进行改写。
-/
example (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  -- 使用代换将目标等式的两侧改写为相同的形式，以便使用等式的反身性来结束证明。
  rewrite [h]
  refl
