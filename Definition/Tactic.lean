import Lean
import Mathlib.Tactic.NthRewrite -- nth_rewrite
import Mathlib.Tactic.LeftRight -- left/right
import Mathlib.Tactic.Use -- use
import Mathlib.Tactic.Cases -- cases
import Std.Tactic.Relation.Symm -- symm

-- open Lean Lean.Expr Lean.Meta
open Lean.Elab.Tactic

@[symm]
theorem Eq.symm' : x = y → y = x := Eq.symm

elab "refl" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    match goalType.eq? with
    | none => throwError "The goal is not an equality"
    | some (_, lhs, rhs) =>
      if (lhs == rhs) then
        evalTactic $ ← `(tactic|rfl)
      else
        throwError "refl tactic failed"
