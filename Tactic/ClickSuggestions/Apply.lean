/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.SectionState

/-!
# Support for `apply` suggestions in `#click_suggestions`
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta ProofWidgets Jsx

/-- The structure for `apply` lemmas stored in the `RefinedDiscrTree`. -/
/-
**Mathlib.Tactic.ClickSuggestions.ApplyLemma** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathli
b.Tactic.ClickSuggestions`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure for `apply` lemmas stored in the `RefinedDiscrTree`.
-/
structure ApplyLemma where
  /-- The lemma -/
  name : Premise

/-- The key that is used for sorting and deduplicating `apply` lemmas. -/
/-
**Mathlib.Tactic.ClickSuggestions.ApplyKey** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.
Tactic.ClickSuggestions`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The key that is used for sorting and deduplicating `apply` lemmas.
-/
structure ApplyKey where
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
instance : Ord ApplyKey where
  compare a b :=
    (compare a.1 b.1).then <|
    (compare a.2 b.2).then <|
    (compare a.3 b.3).then <|
    (compare a.4 b.4)

/-- Whether the two suggestions are duplicates of each other. -/
/-
**Mathlib.Tactic.ClickSuggestions.ApplyKey.isDuplicate** 是 Mathlib 中的一个定义，位于命名空间
 `Mathlib.Tactic.ClickSuggestions.ApplyKey`。
形式化陈述：Mathlib.Tactic.ClickSuggestions.ApplyKey → Mathlib.Tactic.ClickSuggestions
.ApplyKey → MetaM Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whether the two suggestions are duplicates of each other.
-/
def ApplyKey.isDuplicate (a b : ApplyKey) : MetaM Bool :=
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
private def tacticSyntax (lemmaName : Premise) (proof : Expr) (isClosing justLemmaName : Bool) :
    MetaM (TSyntax `tactic) := do
  if justLemmaName then
    let id := mkIdent (← lemmaName.unresolveName)
    -- We can only use `exact` instead of `apply` if the proof has no explicit arguments.
    if ← pure isClosing <&&> hasOnlyImplicitArgs proof then
      `(tactic| exact $id)
    else
      `(tactic| apply $id)
  else
    let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
    if isClosing then
      `(tactic| exact $proof)
    else
      `(tactic| refine $proof)
where
  hasOnlyImplicitArgs (e : Expr) : MetaM Bool := do
    let info ← getFunInfoNArgs e.getAppFn e.getAppNumArgs
    return !info.paramInfo.any (·.binderInfo.isExplicit)

/-- Generate the suggestion for applying `lem`. -/
/-
**Mathlib.Tactic.ClickSuggestions.ApplyLemma.try** 是 Mathlib 中的一个定义，位于命名空间 `Math
lib.Tactic.ClickSuggestions.ApplyLemma`。
形式化陈述：Mathlib.Tactic.ClickSuggestions.ApplyLemma →   Mathlib.Tactic.ClickSuggest
ions.ClickSuggestionsM     (Mathlib.Tactic.ClickSuggestions.Result Mathlib.Tacti
c.ClickSuggestions.ApplyKey)
参数：Mathlib.Tactic.ClickSuggestions.Result Mathlib.Tactic.ClickSuggestions.ApplyK
ey。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generate the suggestion for applying `lem`.
-/
def ApplyLemma.try (lem : ApplyLemma) : ClickSuggestionsM (Result ApplyKey) :=
  withNewMCtxDepth do
  let (proof, mvars, binderInfos, e) ← lem.name.forallMetaTelescopeReducing
  let target ← (← read).goal.getType
  unless ← isDefEq e target do throwError "{e} does not unify with {target}"
  synthAppInstances `click_suggestions default mvars binderInfos false false
  let mut newGoals := #[]
  let mut justLemmaName := true
  for mvar in mvars do
    unless ← mvar.mvarId!.isAssigned do
      if ← isProof mvar <&&> mvar.mvarId!.assumptionCore then
        justLemmaName := false
      else
        newGoals := newGoals.push (← instantiateMVars (← inferType mvar))
  let isClosing := newGoals.isEmpty
  let makesNewMVars := newGoals.any fun goal =>
    (goal.findMVar? (mvars.contains <| .mvar ·)).isSome
  let proof ← instantiateMVars proof
  let key := {
    numGoals := newGoals.size
    nameLength := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr g).pretty.length + s
    name := lem.name.toString
    newGoals := ← newGoals.mapM (abstractMVars ·)
  }
  let tactic ← tacticSyntax lem.name proof (isClosing := isClosing) (justLemmaName := justLemmaName)
  let mut htmls := #[]
  for goal in newGoals do
    htmls := htmls.push <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml goal} </div>
  if isClosing then
    htmls := #[.text "Goal accomplished! 🎉️"]
    addSolvedSuggestion tactic
  let filtered ←
    if !makesNewMVars then
      some <$> mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
    else
      pure none
  htmls := htmls.push <div> {← lem.name.toHtml} </div>
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
  let pattern ← do
    let (_, _, e) ← forallMetaTelescopeReducing (← lem.name.getType)
    exprToHtml e
  return { filtered, unfiltered, key, pattern }

end Mathlib.Tactic.ClickSuggestions

