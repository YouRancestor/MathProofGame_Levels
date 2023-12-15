import Lean.Elab.Tactic

macro "custom_sorry_macro" : tactic => `(tactic| sorry)

example : 1 = 42 := by
  custom_sorry_macro

syntax "custom_tactic" : tactic

example : 42 = 42 := by
  custom_tactic
-- tactic 'tacticCustom_tactic' has not been implemented
  sorry

macro_rules
| `(tactic| custom_tactic) => `(tactic| rfl)

example : 42 = 42 := by
   custom_tactic
-- Goals accomplished 🎉

example : 43 = 43 ∧ 42 = 42:= by
  custom_tactic
-- tactic 'rfl' failed, equality expected
--   43 = 43 ∧ 42 = 42
-- ⊢ 43 = 43 ∧ 42 = 42

macro_rules
| `(tactic| custom_tactic) => `(tactic| apply And.intro <;> custom_tactic)

example : 43 = 43 ∧ 42 = 42 := by
  custom_tactic
-- Goals accomplished 🎉

-- 1. We declare the syntax `and_then`
syntax tactic " and_then " tactic : tactic

-- 2. We write the expander that expands the tactic
--    into running `a`, and then running `b` on all goals produced by `a`.
macro_rules
| `(tactic| $a:tactic and_then $b:tactic) =>
    `(tactic| $a:tactic; all_goals $b:tactic)

-- 3. We test this tactic.
theorem test_and_then: 1 = 1 ∧ 2 = 2 := by
  apply And.intro and_then rfl

#print test_and_then
-- theorem test_and_then : 1 = 1 ∧ 2 = 2 :=
-- { left := Eq.refl 1, right := Eq.refl 2 }

elab "custom_sorry_0" : tactic => do
  return

example : 1 = 2 := by
  custom_sorry_0
-- unsolved goals: ⊢ 1 = 2

elab "custom_sorry_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    dbg_trace f!"goal type: {goalType}"

example : 1 = 2 := by
  custom_sorry_1
-- goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals: ⊢ 1 = 2

elab "custom_sorry_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    Lean.Elab.admitGoal goal

theorem test_custom_sorry : 1 = 2 := by
  custom_sorry_2

#print test_custom_sorry
-- theorem test_custom_sorry : 1 = 2 :=
-- sorryAx (1 = 2) true


elab "custom_assump_0" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    dbg_trace f!"goal type: {goalType}"

example (H1 : 1 = 1) (H2 : 2 = 2): 2 = 2 := by
  custom_assump_0
-- goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals
-- H1 : 1 = 1
-- H2 : 2 = 2
-- ⊢ 2 = 2

example (H1 : 1 = 1): 2 = 2 := by
  custom_assump_0
-- goal type: Eq.{1} Nat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))
-- unsolved goals
-- H1 : 1 = 1
-- ⊢ 2 = 2

elab "list_local_decls_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr}"

example (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_1
-- + local decl: name: test_list_local_decls_1 | expr: _uniq.3339
-- + local decl: name: H1 | expr: _uniq.3340
-- + local decl: name: H2 | expr: _uniq.3341
  rfl

elab "list_local_decls_3" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- Find the type.
      let eq? ← Lean.Meta.isExprDefEq declType goalType -- **NEW** Check if type equals goal type.
      dbg_trace f!"+ local decl[EQUAL? {eq?}]: name: {declName}"

example (H1 : 1 = 1) (H2 : 2 = 2): 1 = 1 := by
  list_local_decls_3
-- + local decl[EQUAL? false]: name: test_list_local_decls_3
-- + local decl[EQUAL? true]: name: H1
-- + local decl[EQUAL? false]: name: H2
  rfl

elab "custom_assump_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let lctx ← Lean.MonadLCtx.getLCtx
    -- Iterate over the local declarations...
    let option_matching_expr ← lctx.findDeclM? fun ldecl: Lean.LocalDecl => do
      let declExpr := ldecl.toExpr -- Find the expression of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- Find the type.
      if (← Lean.Meta.isExprDefEq declType goalType) -- Check if type equals goal type.
      then return some declExpr -- If equal, success!
      else return none          -- Not found.
    dbg_trace f!"matching_expr: {option_matching_expr}"

example (H1 : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by
  custom_assump_1
-- matching_expr: some _uniq.6241
  rfl

example (H1 : 1 = 1) : 2 = 2 := by
  custom_assump_1
-- matching_expr: none
  rfl

elab "custom_assump_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx
    let option_matching_expr ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declType ← Lean.Meta.inferType declExpr
      if ← Lean.Meta.isExprDefEq declType goalType
        then return Option.some declExpr
        else return Option.none
    match option_matching_expr with
    | some e => Lean.Elab.Tactic.closeMainGoal e
    | none =>
      Lean.Meta.throwTacticEx `custom_assump_2 goal
        (m!"unable to find matching hypothesis of type ({goalType})")

example (H1 : 1 = 1) (H2 : 2 = 2) : 2 = 2 := by
  custom_assump_2

example (H1 : 1 = 1): 2 = 2 := by
  custom_assump_2
-- tactic 'custom_assump_2' failed, unable to find matching hypothesis of type (2 = 2)
-- H1 : 1 = 1
-- ⊢ 2 = 2

open Lean.Elab.Tactic in
elab "custom_let " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.define n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

open Lean.Elab.Tactic in
elab "custom_have " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← elabTerm t none
    let v ← elabTermEnsuringType v t
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

theorem test_faq_have : True := by
  custom_let n : Nat := 5
  custom_have h : n = n := rfl
  custom_have n1 : Nat := 5
  custom_let h1 : n = n := rfl
-- n : Nat := 5
-- h : n = n
-- ⊢ True
  trivial

elab "reverse_goals" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goals : List Lean.MVarId ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals goals.reverse

theorem test_reverse_goals : (1 = 2 ∧ 3 = 4) ∧ 5 = 6 := by
  constructor
  constructor
-- case left.left
-- ⊢ 1 = 2
-- case left.right
-- ⊢ 3 = 4
-- case right
-- ⊢ 5 = 6
  reverse_goals
-- case right
-- ⊢ 5 = 6
-- case left.right
-- ⊢ 3 = 4
-- case left.left
-- ⊢ 1 = 2
