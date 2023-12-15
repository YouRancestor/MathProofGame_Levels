import Tutorial.Notation
import Definition.Tactic

/--
### 还原（revert）
**还原**与**引入**（全称量词）相反，它将一个指定的变量从已知条件转化为目标中的全称量词。
-/
example (m : ℕ) (zero_le : ∀ (n : ℕ), 0 ≤ n) : 0 ≤ m := by
  revert m
  exact zero_le
