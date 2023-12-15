import Definition

theorem zero_add (n : ℕ) : 0 + n = n := by
  induction n
  case zero =>
    rewrite [add_zero]
    rewrite [zero_is_0]
    refl
  case succ a ih =>
    rewrite [add_succ]
    rewrite [ih]
    refl
