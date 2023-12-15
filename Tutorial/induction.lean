import Tutorial.Notation
import Definition.Tactic

open Nat in
/--
### 归纳（induction）
有时，已知条件不足以直接证明一条命题，此时我们可以尝试通过归纳法证明它。
#### 归纳原理
对于一条关于自然数的命题P(n:ℕ)，若它同时满足以下两个条件，则这条命题对于任意自然数都是成立的：
1. 它对于自然数0是成立的。即 P(0) 为真。
2. 假如它对于自然数n是成立的，那么它对于自然数n+1也成立。即 P(n) → P(n+1) 。
-/
example (add_zero : ∀ (n ∈ ℕ), n + 0 = n) (add_succ : ∀ (n m : ℕ), n + succ m = succ (n + m)) (zero_is_0 : zero = 0) : 0 + n = n := by
  induction n
  case zero =>
    rewrite [zero_is_0]
    rewrite [add_zero]
    refl
  case succ n h =>
    rewrite [add_succ]
    rewrite [h]
    refl
