import Std.Tactic.Basic -- for Iff.rfl

open Lean.Elab.Tactic in
/--
`refl` tries to close the current goal using reflexivity.
-/
elab "refl" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let type' ← goal.getType'
    -- let type ← goal.getType
    -- dbg_trace f!"type':{type'}\n"
    -- dbg_trace f!"type:{type}\n"
    match type'.eqOrIff? with
    | none => throwError "The goal is not an equality"
    | some (lhs, rhs) =>
      -- dbg_trace f!"l:{lhs},\nr:{rhs}\n"
      if (lhs == rhs) then
        evalTactic $ ← `(tactic|rfl)
      else
        throwError "refl tactic failed"
