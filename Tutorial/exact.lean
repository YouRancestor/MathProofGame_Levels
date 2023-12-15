import Tutorial.Notation
import Definition.Tactic

/--
### 即（exact）
有时，目标已经和已知条件中的某条命题相同，这时可以使用“即”来完成证明。
-/
example (h : y = x + 7) : y = x + 7 := by
  exact h

example (P Q : Type) (p : P) (h : P → Q) : Q := by
  exact h p
