import Tutorial.Notation

/--
### 应用（apply）
在逻辑推理中，我们若有p1的证明，和一个p1→p2的证明p，就可以由p1和p推出p2来得到p2的证明。此时，若证明目标为p2，我们可以对目标**应用**命题p，将目标变转化为证明p2的充分条件p1，再提供p1的证明来完成整个证明过程。
-/
example (x y : ℕ) (h1 : x = 2) (h2 : x = 2 → y = 9) : y = 9 := by
  apply h2
  apply h1
