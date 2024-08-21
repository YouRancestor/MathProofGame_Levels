import Definition.Basic.Tactic

/--
### 自反（refl）
当待证明目标形如 x = x（等式的左右两边完全一样）时，可以使用战术**自反**（表示应用等价关系的自反性）来完成证明。
-/
example : x + 7 = x + 7 := by
  refl
