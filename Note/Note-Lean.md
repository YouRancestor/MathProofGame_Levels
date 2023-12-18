# Lean 笔记

## 符号

- `<|`: 优先级隔断，f $ g $ x 表示 f (g x) 而不是 (f g) x
- `$`: 同 `<|`
- `←`: 
- `=>`:

## 类型

- Lean
    - Parser
        - num/numLit : Parser, numeric literal
        - str/strLit : Parser, string literal
        - ident : Parser, identifier. 有 getId 函数，返回标识符id字符串。
    - Parser.Category
        - term : Category, the builtin syntax category for terms. 在lean的类型论中，一个 term 表示一个表达式，例如 2 + 2 是一个 term。Term 和 Expr 之间的区别在于，Term 是一种 syntax ，而 Expr 是elaboration 的结果。例如，by simp 也是一个 Term ，但它根据不同的上下文， elaborate 为不同的 Expr。
        - tactic : Category, the builtin syntax category for tactics.
    - MVarId
        - withContext 
        - intro (mvarId : MVarId) (name : Name) : MetaM (FVarId × MVarId), 引入一个 binder 并使用 name 作为新假设的名字。
        - getType (mvarId : MVarId) : MetaM Expr, 获取给定的 metavariable 的类型。
    - Elab
        - Term
            - elabType (stx : Syntax) : TermElabM Expr, Elaborate stx.
        - Tactic
            - replaceMainGoal (mvarIds : List MVarId) : TacticM Unit, 丢弃第一个目标，并替换为 mvarIds 中给定的目标。
            - evalTactic (stx : Syntax) : TacticM Unit, 执行 stx 表示的 tactic。
    - Meta
        - mkFreshExprMVar (type? : Option Expr) (kind : MetavarKind := MetavarKind.natural) (userName : Name := Name.anonymous) : MetaM Expr

## 构建

### Rebuild Imports

lake "print-paths" "Init" "{imports}"

例：
```bat
lake "print-paths" "Init" "Definition" "Collection.succ_eq_add_one" "Collection.add_comm"
```
