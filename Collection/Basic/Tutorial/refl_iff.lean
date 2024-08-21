import Definition.Basic.Tactic

/--
### 自反（refl）
当待证明目标形如 p ↔ p（逻辑等价式的左右两边完全一样） 时，也可以使用战术**自反**来完成证明。
-/
example : p ↔ p := by
  refl
