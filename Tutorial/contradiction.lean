import Tutorial.Notation
-- import Definition.Tactic

/--
### 矛盾（contradiction）
当假设中含有一对矛盾的命题 p 和 ¬p 时，可以使用“矛盾”来完成证明。
-/
example (p q : Prop) (h : p) (h' : ¬p) : q := by
  contradiction
