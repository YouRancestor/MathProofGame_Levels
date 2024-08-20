
/--
### 拆分（当且仅当）(constructor)
对于“当且仅当（iff）”（if and only if）型目标 P ↔ Q ，使用**拆分**将其分解为为 P 和 Q 两个子目标，然后分别证明。
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
