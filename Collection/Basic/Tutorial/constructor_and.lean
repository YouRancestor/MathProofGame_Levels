
/--
### 拆分（且）(constructor)
对于且型目标 P ∧ Q ，使用**拆分**将其分解为 P 和 Q 两个子目标，然后分别证明。
-/
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  case left =>
    exact p
  case right =>
    exact q
