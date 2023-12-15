import Lean

macro x:ident ":" t:term " ↦ " y:term : term => do
  `(fun $x : $t => $y)

-- #eval (x : Nat ↦ x + 2) 2 -- 4

macro x:ident " ↦ " y:term : term => do
  `(fun $x  => $y)

#check (x ↦  x + 2)

elab "#assertType " termStx:term " : " typeStx:term : command =>
  open Lean Lean.Elab Command Term in
  liftTermElabM
    try
      let tp ← elabType typeStx
      discard $ elabTermEnsuringType termStx tp
      synthesizeSyntheticMVarsNoPostponing
      logInfo "success"
    catch
    | _ => throwError "failure"

-- #assertType 5  : Nat -- success
-- #assertType [] : Nat -- failure
-- #assertType 5  : ?_

inductive Arith : Type where
| add : Arith → Arith → Arith -- e + f
| mul : Arith → Arith → Arith -- e * f
| nat : Nat → Arith           -- constant
| var : String → Arith        -- variable

declare_syntax_cat arith
syntax num : arith -- nat for Arith.nat
syntax str : arith -- strings for Arith.var
syntax:50 arith:50 "+" arith:51 : arith -- Arith.add
syntax:60 arith:60 "*" arith:61 : arith -- Arith.mul
syntax "(" arith ")" : arith -- bracketed expressions

-- Auxiliary notation for translating `arith` into `term`
syntax " ⟪ " arith " ⟫ " : term

macro_rules
| `( ⟪ $s:str ⟫ ) => `( Arith.var $s )
| `( ⟪ $n:num ⟫ ) => `( Arith.nat $n )
| `( ⟪ $e:arith + $f:arith ⟫ ) => `( Arith.add ⟪ $e ⟫ ⟪ $f ⟫ )
| `( ⟪ $e:arith * $f:arith ⟫ ) => `( Arith.mul ⟪ $e ⟫ ⟪ $f ⟫ )
| `( ⟪ ( $e ) ⟫ ) => `( ⟪ $e ⟫ )

-- #check ⟪ "x" * "y" ⟫
-- #check ⟪ "x" + "y" ⟫
-- #check ⟪ 5 + "x" ⟫
-- #check ⟪ "x" + "y" * "z" ⟫
-- #check ⟪ "x" * "y" + "z" ⟫
-- #check ⟪ ("x" + "y") * "z" ⟫

open Lean Meta Elab Tactic Term in
elab "suppose" n:ident ":" t:term : tactic => do
  let n : Name := n.getId
  let mvarId ← getMainGoal
  mvarId.withContext do
    let tType ← elabType t
    let p ← mkFreshExprMVar tType MetavarKind.syntheticOpaque n
    let (_, mvarIdNew) ← MVarId.intro (← mvarId.assert n tType p) n
    replaceMainGoal [p.mvarId!, mvarIdNew]
    let newType ← mvarIdNew.getType
    dbg_trace s!"n:{n}\nt: {t}\ntType:{tType}\np: {p}\nnewType:{newType}\n"
  evalTactic $ ← `(tactic|rotate_left)

example : 0 + a = a := by
  suppose add_comm : 0 + a = a + 0
  rw [add_comm]
  rw [Nat.add_zero]
  exact Nat.add_comm 0 a
