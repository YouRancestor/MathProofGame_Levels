import Tutorial.Notation
import Tactic.nth_rewrite
import Tactic.refl

open Nat in
/--
### 指定代换（nth_rewrite）
当目标中有两个以上相同的部分时，使用代换指令会将匹配的所有相同的部分全部替换。若只想替换其中的某一个，可以使用*指定代换*，指定要替换的序号。
-/
example (one_eq_succ_zero : 1 = Nat.succ 0) (add_succ : ∀ (a : Nat) (b : Nat), a + b.succ = Nat.succ (a + b)) (add_zero : ∀ (n ∈ ℕ),  n + 0 = n) : 1 + 1 = Nat.succ 1 := by
  -- 使用指定代换，完成证明
  nth_rewrite 2 [one_eq_succ_zero]
  nth_rewrite 2 [←add_zero 1]
  rewrite [add_succ]
  refl
