import Definition.Basic.Tutorial.Notation

/--
### 引入（intro）
当目标形如 P → Q 时，我们可以**引入**一个假设 h : P ，然后利用它来推出 Q 以完成证明。
-/
example (x : ℕ) : x = 2 → x = 2 := by
  intro h
  exact h
