import Definition.Basic.Tactic

/--
### 虚假前提（exfalso）
相互矛盾的前提可以推导出一切命题。若已知条件（假设/定理）中存在矛盾，则任何目标都为真，因此无需证明目标，只需指出已知条件中的矛盾所在即可。使用**虚假前提**将目标转化为False（假），以便从现有条件推出False，说明从已知条件中可推出假，也就是假设不成立，假设中存在矛盾。
-/
example (P Q : Prop) : (P ∧ ¬P) → Q := by
  -- 用矛盾的 P 和 ¬P 可以推出任意命题 Q
  intro h
  cases h
  case intro h_left h_right =>
    exfalso
    case h =>
      apply h_right
      exact h_left
