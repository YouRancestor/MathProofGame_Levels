import Definition.Basic.Tutorial.Notation
import Definition.Basic.Tactic

/--
### 全称量词
当目标含有全称量词（∀）时，我们可以通过**引入**一个假设来消去全称量词，然后利用它来完成证明。
-/
example : ∀ (a b : ℕ) , a + b = a + b  := by
  intro a
  intro b
  refl
