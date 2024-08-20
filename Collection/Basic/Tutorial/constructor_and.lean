
/--
### 分解（且）(constructor)
对于且型目标 P ∧ Q ，使用**分解**将 ∧ 号连接的 P 和 Q 构造为两个子目标，然后分别证明。
-/
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  case left =>
    exact p
  case right =>
    exact q
