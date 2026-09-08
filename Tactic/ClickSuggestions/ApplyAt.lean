/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.SectionState
public import Mathlib.Tactic.ApplyAt

/-!
# Support for `apply at` suggestions in `#click_suggestions`
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta ProofWidgets Jsx

/-- The structure for `apply at` lemmas stored in the `RefinedDiscrTree`. -/
/-
**Mathlib.Tactic.ClickSuggestions.ApplyAtLemma** 是 Mathlib 中的一个归纳类型，位于命名空间 `Math
lib.Tactic.ClickSuggestions`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure for `apply at` lemmas stored in the `RefinedDiscrTree`.
-/
structure ApplyAtLemma where
  /-- The lemma -/
  name : Premise

/-- The key that is used for sorting and deduplicating `apply at` lemmas. -/
/-
**Mathlib.Tactic.ClickSuggestions.ApplyAtKey** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathli
b.Tactic.ClickSuggestions`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The key that is used for sorting and deduplicating `apply at` lemmas.
-/
structure ApplyAtKey where
  /-- How many new goals are generated. -/
  numGoals : Nat
  /-- The name length of the used lemma. -/
  nameLength : Nat
  /-- The total length of the new goals when printed. -/
  replacementSize : Nat
  /-- The name of the used lemma. -/
  name : String
  /-- The new goals. -/
  newGoals : Array AbstractMVarsResult
deriving Inhabited
/-
**Mathlib.Tactic.ClickSuggestions.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Cli
ckSuggestions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ord ApplyAtKey where
  compare a b :=
    (compare a.1 b.1).then <|
    (compare a.2 b.2).then <|
    (compare a.3 b.3).then <|
    (compare a.4 b.4)

/-- Whether the two suggestions are duplicates of each other. -/
/-
**Mathlib.Tactic.ClickSuggestions.ApplyAtKey.isDuplicate** 是 Mathlib 中的一个定义，位于命名
空间 `Mathlib.Tactic.ClickSuggestions.ApplyAtKey`。
形式化陈述：Mathlib.Tactic.ClickSuggestions.ApplyAtKey → Mathlib.Tactic.ClickSuggestio
ns.ApplyAtKey → MetaM Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whether the two suggestions are duplicates of each other.
-/
def ApplyAtKey.isDuplicate (a b : ApplyAtKey) : MetaM Bool :=
  pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

/-- Return the `apply` tactic that performs the application. -/
/-
**Mathlib.Tactic.ClickSuggestions.tacticSyntax** 是 Mathlib 中的一个定义，位于命名空间 `Mathli
b.Tactic.ClickSuggestions`。
形式化陈述：tacticSyntax (e eNew : Expr) (rwKind : RwKind) : ClickSuggestionsM (TSynta
x `tactic)
参数：e eNew : Expr；rwKind : RwKind。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return the `apply` tactic that performs the application.
-/
private def tacticSyntax (lem : ApplyAtLemma) : ClickSuggestionsM (TSyntax `tactic) := do
  -- let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab app.proof)
  `(tactic| apply $(mkIdent (← lem.name.unresolveName)) at $(← getHypIdent!))

/-- Generate the suggestion for applying `lem`. -/
/-
**Mathlib.Tactic.ClickSuggestions.ApplyAtLemma.try** 是 Mathlib 中的一个定义，位于命名空间 `Ma
thlib.Tactic.ClickSuggestions.ApplyAtLemma`。
形式化陈述：Mathlib.Tactic.ClickSuggestions.ApplyAtLemma →   Mathlib.Tactic.ClickSugge
stions.ClickSuggestionsM     (Mathlib.Tactic.ClickSuggestions.Result Mathlib.Tac
tic.ClickSuggestions.ApplyAtKey)
参数：Mathlib.Tactic.ClickSuggestions.Result Mathlib.Tactic.ClickSuggestions.ApplyA
tKey。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generate the suggestion for applying `lem`.
-/
def ApplyAtLemma.try (lem : ApplyAtLemma) : ClickSuggestionsM (Result ApplyAtKey) :=
  withNewMCtxDepth do
  let (_proof, mvars, binderInfos, replacement) ← lem.name.forallMetaTelescopeReducing
  let mvar := mvars.back!
  let mvars := mvars.pop
  let fvarId := (← read).hyp?.get!
  unless ← isDefEq mvar (.fvar fvarId) do
    throwError "{← inferType mvar} does not unify with {← fvarId.getType}"
  synthAppInstances `click_suggestions default mvars binderInfos false false
  let mut newGoals := #[]
  for mvar in mvars do
    unless ← mvar.mvarId!.isAssigned do
      newGoals := newGoals.push (← instantiateMVars (← inferType mvar))

  let replacement ← instantiateMVars replacement
  let makesNewMVars :=
    (replacement.findMVar? (mvars.contains <| .mvar ·)).isSome ||
    newGoals.any fun goal ↦ (goal.findMVar? (mvars.contains <| .mvar ·)).isSome
  let key := {
    numGoals := newGoals.size
    nameLength := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr g).pretty.length + s
    name := lem.name.toString
    newGoals := (← newGoals.mapM (abstractMVars ·)).push (← abstractMVars replacement)
  }
  let tactic ← tacticSyntax lem
  let mut htmls := #[← exprToHtml replacement]
  for goal in newGoals do
    htmls := htmls.push <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml goal} </div>
  let filtered ←
    if makesNewMVars then
      pure none
    else
      some <$> mkSuggestion tactic (.element "div" #[] htmls)
  htmls := htmls.push <div> {← lem.name.toHtml} </div>
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls)
  let pattern ← do
    let (xs, _, _) ← forallMetaTelescopeReducing (← lem.name.getType)
    exprToHtml (← inferType xs.back!)
  return { filtered, unfiltered, key, pattern }

end Mathlib.Tactic.ClickSuggestions

