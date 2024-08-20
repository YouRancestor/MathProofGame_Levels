import Definition.Basic.Tutorial.Notation
import Definition.Basic.Tactic

/--
### 使用（use）
当目标含有存在量词（∃）时，可以通过**使用（use）**提供一个使目标命题成立的变量值，从而消去存在量词，完成证明。
-/

example : ∃ x : ℕ, x = 2 := /- ⟨2, rfl⟩-/ by
  use 2
