import Std.Tactic.Relation.Symm -- symm

@[symm]
theorem Eq.symm'?' : x = y → y = x := Eq.symm
@[symm]
theorem Ne.symm'?' : x ≠ y → y ≠ x := Ne.symm
