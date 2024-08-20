import Definition.Basic.Tutorial.Notation
import Definition.Basic.Tactic

/--
### 对称（symm）
基于等价关系的对称性，**对称**将一个等式的两边交换。
-/
example (x y : Nat) (h : x = y) : y = x := by
  -- symm
  symm at h
  exact h
