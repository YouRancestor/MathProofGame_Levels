
/--
### 分解（等价）(constructor)
对于等价（当且仅当）型目标 P ↔ Q ，使用**分解**将 ↔ 号连接的 P 和 Q 构造为两个子目标，然后分别证明。
-/
example : P ∧ Q ↔ Q ∧ P := by
  constructor
  case mp =>
    intro h
    cases h
    case intro p q =>
    constructor
    case left =>
      exact q
    case right =>
      exact p
  case mpr =>
    intro h
    cases h
    case intro p q =>
    constructor
    case left =>
      exact q
    case right =>
      exact p
