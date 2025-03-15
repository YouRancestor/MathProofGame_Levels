import Definition.Basic.Tutorial.Notation
import Definition.Basic.Tactic

open Nat
/--
### 归纳（induction）
有时，已知条件不足以直接证明一条命题，此时可以尝对变量进行归纳来证明它。

#### 归纳原理
对于一条关于自然数的命题p(n:ℕ)，若它同时满足以下两个条件，则这条命题对于任意自然数都是成立的：
1. 它对于自然数0是成立的。即 p(0) 为真。
2. 假如它对于自然数n是成立的，那么它对于自然数n+1也成立。即 p(n) → p(n+1) 。

战术**归纳**对指定变量使用归纳法，将当前目标转化为两个新目标再分别证明，两个新目标分别对应于上述归纳原理中的1和2两个条件，同时对于条件2对应的情形，引入归纳假设 h : p(n) → p(n+1)。
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
