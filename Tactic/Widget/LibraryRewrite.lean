/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Anand Rao
-/
module

public meta import Mathlib.Lean.Meta.RefinedDiscrTree
public meta import Mathlib.Tactic.Widget.SelectPanelUtils
public meta import Mathlib.Lean.GoalsLocation
public meta import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Tactic.NthRewrite
public import ProofWidgets.Component.FilterDetails
public import ProofWidgets.Component.OfRpcMethod

/-!
# Point & click library rewriting

This file defines `rw??`, an interactive tactic that suggests rewrites for any expression selected
by the user.

`rw??` uses a (lazy) `RefinedDiscrTree` to lookup a list of candidate rewrite lemmas.
It excludes lemmas that are automatically generated.
Each lemma is then checked one by one to see whether it is applicable.
For each lemma that works, the corresponding rewrite tactic is constructed
and converted into a `String` that fits inside mathlib's 100 column limit,
so that it can be pasted into the editor when selected by the user.

The `RefinedDiscrTree` lookup groups the results by match pattern and gives a score to each pattern.
This is used to display the results in sections. The sections are ordered by this score.
Within each section, the lemmas are sorted by
- rewrites with fewer extra goals come first
- left-to-right rewrites come first
- shorter lemma names come first
- shorter replacement expressions come first (when taken as a string)
- alphabetically ordered by lemma name

The lemmas are optionally filtered to avoid duplicate rewrites, or trivial rewrites. This
is controlled by the filter button on the top right of the results.

When a rewrite lemma introduces new goals, these are shown after a `⊢`.

## TODO

Ways to improve `rw??`:
- Improve the logic around `nth_rw` and occurrences,
  and about when to pass explicit arguments to the rewrite lemma.
  For example, we could only pass explicit arguments if that avoids using `nth_rw`.
  Performance may be a limiting factor for this.
  Currently, the occurrence is computed by `viewKAbstractSubExpr`.
- Modify the interface to allow creating a whole `rw [.., ..]` chain, without having to go into
  the editor in between. For this to work, we will need a more general syntax,
  something like `rw [..]??`, which would be pasted into the editor.
- We could look for rewrites of partial applications of the selected expression.
  For example, when clicking on `(f + g) x`, there should still be an `add_comm` suggestion.

Ways to extend `rw??`:
- Support generalized rewriting (`grw`)
- Integrate rewrite search with the `calc?` widget so that a `calc` block can be created using
  just point & click.

-/

public meta section

/-! ### Caching -/

namespace Mathlib.Tactic.LibraryRewrite

open Lean Meta RefinedDiscrTree

/-- The structure for rewrite lemmas stored in the `RefinedDiscrTree`. -/
/-
**Mathlib.Tactic.LibraryRewrite.RewriteLemma** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathli
b.Tactic.LibraryRewrite`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure for rewrite lemmas stored in the `RefinedDiscrTree`.
-/
structure RewriteLemma where
  /-- The name of the lemma -/
  name : Name
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
deriving BEq, Inhabited
/-
**Mathlib.Tactic.LibraryRewrite.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Libra
ryRewrite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ToFormat RewriteLemma where
  format lem := f! "{if lem.symm then "← " else ""}{lem.name}"

/-- Return `true` if `s` and `t` are equal up to changing the `MVarId`s. -/
/-
**Mathlib.Tactic.LibraryRewrite.isMVarSwap** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ta
ctic.LibraryRewrite`。
形式化陈述：isMVarSwap (t s : Expr) : Bool
参数：t s : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return `true` if `s` and `t` are equal up to changing the `MVarId`s.
-/
def isMVarSwap (t s : Expr) : Bool :=
  go t s {} |>.isSome
where
  /-- The main loop of `isMVarSwap`. Returning `none` corresponds to a failure. -/
  go (t s : Expr) (swaps : List (MVarId × MVarId)) : Option (List (MVarId × MVarId)) := do
  let isTricky e := e.hasExprMVar || e.hasLevelParam
  if isTricky t then
    guard (isTricky s)
    match t, s with
    -- Note we don't bother keeping track of universe level metavariables.
    | .const n₁ _       , .const n₂ _        => guard (n₁ == n₂); some swaps
    | .sort _           , .sort _            => some swaps
    | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => go d₁ d₂ swaps >>= go b₁ b₂
    | .lam _ d₁ b₁ _    , .lam _ d₂ b₂ _     => go d₁ d₂ swaps >>= go b₁ b₂
    | .mdata d₁ e₁      , .mdata d₂ e₂       => guard (d₁ == d₂); go e₁ e₂ swaps
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => go t₁ t₂ swaps >>= go v₁ v₂ >>= go b₁ b₂
    | .app f₁ a₁        , .app f₂ a₂         => go f₁ f₂ swaps >>= go a₁ a₂
    | .proj n₁ i₁ e₁    , .proj n₂ i₂ e₂     => guard (n₁ == n₂ && i₁ == i₂); go e₁ e₂ swaps
    | .fvar fvarId₁     , .fvar fvarId₂      => guard (fvarId₁ == fvarId₂); some swaps
    | .lit v₁           , .lit v₂            => guard (v₁ == v₂); some swaps
    | .bvar i₁          , .bvar i₂           => guard (i₁ == i₂); some swaps
    | .mvar mvarId₁     , .mvar mvarId₂      =>
      match swaps.find? (·.1 == mvarId₁) with
      | none =>
        guard (swaps.all (·.2 != mvarId₂))
        let swaps := (mvarId₁, mvarId₂) :: swaps
        if mvarId₁ == mvarId₂ then
          some swaps
        else
          some <| (mvarId₂, mvarId₁) :: swaps
      | some (_, mvarId) => guard (mvarId == mvarId₂); some swaps
    | _                 , _                  => none
  else
    guard (t == s); some swaps

/-- Extract the left and right-hand sides of an equality or iff statement. -/
/-
**Mathlib.Tactic.LibraryRewrite.eqOrIff** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tacti
c.LibraryRewrite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the left and right-hand sides of an equality or iff statement.
-/
@[inline] def eqOrIff? (e : Expr) : Option (Expr × Expr) :=
  match e.eq? with
  | some (_, lhs, rhs) => some (lhs, rhs)
  | none => e.iff?

/-- Try adding the lemma to the `RefinedDiscrTree`. -/
/-
**Mathlib.Tactic.LibraryRewrite.addRewriteEntry** 是 Mathlib 中的一个定义，位于命名空间 `Mathl
ib.Tactic.LibraryRewrite`。
形式化陈述：addRewriteEntry (name : Name) (cinfo : ConstantInfo) : MetaM (List (Rewrit
eLemma × List (Key × LazyEntry)))
参数：name : Name；cinfo : ConstantInfo。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Try adding the lemma to the `RefinedDiscrTree`.
-/
def addRewriteEntry (name : Name) (cinfo : ConstantInfo) :
    MetaM (List (RewriteLemma × List (Key × LazyEntry))) := do
  -- we start with a fast-failing check to see if the lemma has the right shape
  let .const head _ := cinfo.type.getForallBody.getAppFn | return []
  unless head == ``Eq || head == ``Iff do return []
  setMCtx {} -- recall that the metavariable context is not guaranteed to be empty at the start
  let (_, _, eqn) ← forallMetaTelescope cinfo.type
  let some (lhs, rhs) := eqOrIff? eqn | return []
  let badMatch e :=
    e.getAppFn.isMVar ||
    -- this extra check excludes general equality lemmas that apply at any equality
    -- these are almost never useful, and there are very many of them.
    e.eq?.any fun (α, l, r) =>
      α.getAppFn.isMVar && l.getAppFn.isMVar && r.getAppFn.isMVar && l != r
  if badMatch lhs then
    if badMatch rhs then
      return []
    else
      return [({ name, symm := true }, ← initializeLazyEntryWithEta rhs)]
  else
    let result := ({ name, symm := false }, ← initializeLazyEntryWithEta lhs)
    if badMatch rhs || isMVarSwap lhs rhs then
      return [result]
    else
      return [result, ({ name, symm := true }, ← initializeLazyEntryWithEta rhs)]


/-- Try adding the local hypothesis to the `RefinedDiscrTree`. -/
/-
**Mathlib.Tactic.LibraryRewrite.addLocalRewriteEntry** 是 Mathlib 中的一个定义，位于命名空间 `
Mathlib.Tactic.LibraryRewrite`。
形式化陈述：addLocalRewriteEntry (decl : LocalDecl) : MetaM (List ((FVarId × Bool) × L
ist (Key × LazyEntry)))
参数：decl : LocalDecl。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Try adding the local hypothesis to the `RefinedDiscrTree`.
-/
def addLocalRewriteEntry (decl : LocalDecl) :
    MetaM (List ((FVarId × Bool) × List (Key × LazyEntry))) := do
  -- The transparency is set to `reducible`. Stronger reduction may give unexpected results.
  let (_, _, eqn) ← forallMetaTelescopeReducing decl.type
  let some (lhs, rhs) := eqOrIff? (← whnf eqn) | return []
  let result := ((decl.fvarId, false), ← initializeLazyEntryWithEta lhs)
  return [result, ((decl.fvarId, true), ← initializeLazyEntryWithEta rhs)]
/-
**Mathlib.Tactic.LibraryRewrite.ExtState** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Ta
ctic.LibraryRewrite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private abbrev ExtState := IO.Ref (Option (RefinedDiscrTree RewriteLemma))

private initialize ExtState.default : ExtState ←
  IO.mkRef none
/-
**Mathlib.Tactic.LibraryRewrite.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Libra
ryRewrite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance : Inhabited ExtState where
  default := ExtState.default

private initialize importedRewriteLemmasExt : EnvExtension ExtState ←
  registerEnvExtension (IO.mkRef none)



/-! ### Computing the Rewrites -/

/-- Get all potential rewrite lemmas from the imported environment.
By setting the `librarySearch.excludedModules` option, all lemmas from certain modules
can be excluded. -/
/-
**Mathlib.Tactic.LibraryRewrite.getImportCandidates** 是 Mathlib 中的一个定义，位于命名空间 `M
athlib.Tactic.LibraryRewrite`。
形式化陈述：getImportCandidates (e : Expr) : MetaM (Array (Array RewriteLemma))
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get all potential rewrite lemmas from the imported environment.
By setting the `librarySearch.excludedModules` option, all lemmas from certain m
odules
can be excluded.
-/
def getImportCandidates (e : Expr) : MetaM (Array (Array RewriteLemma)) := do
  let matchResult ← findImportMatches importedRewriteLemmasExt addRewriteEntry
    /-
    5000 constants seems to be approximately the right number of tasks
    Too many means the tasks are too long.
    Too few means less cache can be reused and more time is spent on combining different results.

    With 5000 constants per task, we set the `HashMap` capacity to 256,
    which is the largest capacity it gets to reach.
    -/
    (constantsPerTask := 5000) (capacityPerTask := 256) e
  return matchResult.flatten

/-- Get all potential rewrite lemmas from the current file. Exclude lemmas from modules
in the `librarySearch.excludedModules` option. -/
/-
**Mathlib.Tactic.LibraryRewrite.getModuleCandidates** 是 Mathlib 中的一个定义，位于命名空间 `M
athlib.Tactic.LibraryRewrite`。
形式化陈述：getModuleCandidates (e : Expr) : MetaM (Array (Array RewriteLemma))
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get all potential rewrite lemmas from the current file. Exclude lemmas from modu
les
in the `librarySearch.excludedModules` option.
-/
def getModuleCandidates (e : Expr) : MetaM (Array (Array RewriteLemma)) := do
  let moduleTreeRef ← createModuleTreeRef addRewriteEntry
  let matchResult ← findModuleMatches moduleTreeRef e
  return matchResult.flatten


/-- A rewrite lemma that has been applied to an expression. -/
/-
**Mathlib.Tactic.LibraryRewrite.Rewrite** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tac
tic.LibraryRewrite`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A rewrite lemma that has been applied to an expression.
-/
structure Rewrite where
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
  /-- The proof of the rewrite -/
  proof : Expr
  /-- The replacement expression obtained from the rewrite -/
  replacement : Expr
  /-- The size of the replacement when printed -/
  stringLength : Nat
  /-- The extra goals created by the rewrite -/
  extraGoals : Array (MVarId × BinderInfo)
  /-- Whether the rewrite introduces a new metavariable in the replacement expression. -/
  makesNewMVars : Bool

/-- If `thm` can be used to rewrite `e`, return the rewrite. -/
/-
**Mathlib.Tactic.LibraryRewrite.checkRewrite** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.
Tactic.LibraryRewrite`。
形式化陈述：checkRewrite (thm e : Expr) (symm : Bool) : MetaM (Option Rewrite)
参数：thm e : Expr；symm : Bool。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `thm` can be used to rewrite `e`, return the rewrite.
-/
def checkRewrite (thm e : Expr) (symm : Bool) : MetaM (Option Rewrite) := do
  withTraceNodeBefore `rw?? (fun _ => return m!
    "rewriting {e} by {if symm then "← " else ""}{thm}") do
  let (mvars, binderInfos, eqn) ← forallMetaTelescopeReducing (← inferType thm)
  let some (lhs, rhs) := eqOrIff? (← whnf eqn) |
    throwError "Expected equation, not {indentExpr eqn}"
  let (lhs, rhs) := if symm then (rhs, lhs) else (lhs, rhs)
  let unifies ← withTraceNodeBefore `rw?? (fun _ =>return m! "unifying {e} =?= {lhs}")
    (withReducible (isDefEq lhs e))
  unless unifies do return none
  -- just like in `kabstract`, we compare the `HeadIndex` and number of arguments
  let lhs ← instantiateMVars lhs
  if lhs.toHeadIndex != e.toHeadIndex || lhs.headNumArgs != e.headNumArgs then
    return none
  synthAppInstances `rw?? default mvars binderInfos false false
  let mut extraGoals := #[]
  for mvar in mvars, bi in binderInfos do
    unless ← mvar.mvarId!.isAssigned do
      extraGoals := extraGoals.push (mvar.mvarId!, bi)

  let replacement ← instantiateMVars rhs
  let stringLength := (← ppExpr replacement).pretty.length
  let makesNewMVars := (replacement.findMVar? fun mvarId => mvars.any (·.mvarId! == mvarId)).isSome
  let proof ← instantiateMVars (mkAppN thm mvars)
  return some { symm, proof, replacement, stringLength, extraGoals, makesNewMVars }

initialize
  registerTraceClass `rw??

/-- Try to rewrite `e` with each of the rewrite lemmas, and sort the resulting rewrites. -/
/-
**Mathlib.Tactic.LibraryRewrite.checkAndSortRewriteLemmas** 是 Mathlib 中的一个定义，位于命
名空间 `Mathlib.Tactic.LibraryRewrite`。
形式化陈述：checkAndSortRewriteLemmas (e : Expr) (rewrites : Array RewriteLemma) : Met
aM (Array (Rewrite × Name))
参数：e : Expr；rewrites : Array RewriteLemma。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Try to rewrite `e` with each of the rewrite lemmas, and sort the resulting rewri
tes.
-/
def checkAndSortRewriteLemmas (e : Expr) (rewrites : Array RewriteLemma) :
    MetaM (Array (Rewrite × Name)) := do
  let rewrites ← rewrites.filterMapM fun rw =>
    tryCatchRuntimeEx do
        let thm ← mkConstWithFreshMVarLevels rw.name
        Option.map (·, rw.name) <$> checkRewrite thm e rw.symm
      fun _ =>
        return none
  let lt (a b : (Rewrite × Name)) := Ordering.isLT <|
    (compare a.1.extraGoals.size b.1.extraGoals.size).then <|
    (compare a.1.symm b.1.symm).then <|
    (compare a.2.toString.length b.2.toString.length).then <|
    (compare a.1.stringLength b.1.stringLength).then <|
    (Name.cmp a.2 b.2)
  return rewrites.qsort lt

/-- Return all applicable library rewrites of `e`.
Note that the result may contain duplicate rewrites. These can be removed with `filterRewrites`. -/
/-
**Mathlib.Tactic.LibraryRewrite.getImportRewrites** 是 Mathlib 中的一个定义，位于命名空间 `Mat
hlib.Tactic.LibraryRewrite`。
形式化陈述：getImportRewrites (e : Expr) : MetaM (Array (Array (Rewrite × Name)))
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return all applicable library rewrites of `e`.
Note that the result may contain duplicate rewrites. These can be removed with `
filterRewrites`.
-/
def getImportRewrites (e : Expr) : MetaM (Array (Array (Rewrite × Name))) := do
  (← getImportCandidates e).mapM (checkAndSortRewriteLemmas e)

/-- Same as `getImportRewrites`, but for lemmas from the current file. -/
/-
**Mathlib.Tactic.LibraryRewrite.getModuleRewrites** 是 Mathlib 中的一个定义，位于命名空间 `Mat
hlib.Tactic.LibraryRewrite`。
形式化陈述：getModuleRewrites (e : Expr) : MetaM (Array (Array (Rewrite × Name)))
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Same as `getImportRewrites`, but for lemmas from the current file.
-/
def getModuleRewrites (e : Expr) : MetaM (Array (Array (Rewrite × Name))) := do
  (← getModuleCandidates e).mapM (checkAndSortRewriteLemmas e)

/-! ### Rewriting by hypotheses -/

/-- Construct the `RefinedDiscrTree` of all local hypotheses. -/
/-
**Mathlib.Tactic.LibraryRewrite.getHypotheses** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib
.Tactic.LibraryRewrite`。
形式化陈述：getHypotheses (except : Option FVarId) : MetaM (RefinedDiscrTree (FVarId ×
 Bool))
参数：except : Option FVarId。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the `RefinedDiscrTree` of all local hypotheses.
-/
def getHypotheses (except : Option FVarId) : MetaM (RefinedDiscrTree (FVarId × Bool)) :=
  withReducible do
  let mut tree : PreDiscrTree (FVarId × Bool) := {}
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && except.all (· != decl.fvarId) then
      for (val, entries) in ← addLocalRewriteEntry decl do
        for (key, entry) in entries do
          tree := tree.push key (entry, val)
  return tree.toRefinedDiscrTree

/-- Return all applicable hypothesis rewrites of `e`. Similar to `getImportRewrites`. -/
/-
**Mathlib.Tactic.LibraryRewrite.getHypothesisRewrites** 是 Mathlib 中的一个定义，位于命名空间 
`Mathlib.Tactic.LibraryRewrite`。
形式化陈述：getHypothesisRewrites (e : Expr) (except : Option FVarId) : MetaM (Array (
Array (Rewrite × FVarId)))
参数：e : Expr；except : Option FVarId。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return all applicable hypothesis rewrites of `e`. Similar to `getImportRewrites`
.
-/
def getHypothesisRewrites (e : Expr) (except : Option FVarId) :
    MetaM (Array (Array (Rewrite × FVarId))) := do
  let (candidates, _) ← (← getHypotheses except).getMatch e (unify := false) (matchRootStar := true)
  let candidates := candidates.flatten
  candidates.mapM <| Array.filterMapM fun (fvarId, symm) =>
    tryCatchRuntimeEx do
      Option.map (·, fvarId) <$> checkRewrite (.fvar fvarId) e symm
    fun _ =>
      return none

/-! ### Filtering out duplicate lemmas -/

/-- Get the `BinderInfo`s for the arguments of `mkAppN fn args`. -/
/-
**Mathlib.Tactic.LibraryRewrite.getBinderInfos** 是 Mathlib 中的一个定义，位于命名空间 `Mathli
b.Tactic.LibraryRewrite`。
形式化陈述：getBinderInfos (fn : Expr) (args : Array Expr) : MetaM (Array BinderInfo)
参数：fn : Expr；args : Array Expr。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_lt_one`：0 < 1

--- 原说明 ---
Get the `BinderInfo`s for the arguments of `mkAppN fn args`.
-/
def getBinderInfos (fn : Expr) (args : Array Expr) : MetaM (Array BinderInfo) := do
  let mut fnType ← inferType fn
  let mut result := Array.mkEmpty args.size
  let mut j := 0
  for i in [:args.size] do
    unless fnType.isForall do
      fnType ← whnfD (fnType.instantiateRevRange j i args)
      j := i
    let .forallE _ _ b bi := fnType | throwError m! "expected function type {indentExpr fnType}"
    fnType := b
    result := result.push bi
  return result

/-- Determine whether the explicit parts of two expressions are equal,
and the implicit parts are definitionally equal. -/
/-
**Mathlib.Tactic.LibraryRewrite.isExplicitEq** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathl
ib.Tactic.LibraryRewrite`。
形式化陈述：Expr → Expr → MetaM Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Determine whether the explicit parts of two expressions are equal,
and the implicit parts are definitionally equal.
-/
partial def isExplicitEq (t s : Expr) : MetaM Bool := do
  if t == s then
    return true
  unless t.getAppNumArgs == s.getAppNumArgs && t.getAppFn == s.getAppFn do
    return false
  let tArgs := t.getAppArgs
  let sArgs := s.getAppArgs
  let bis ← getBinderInfos t.getAppFn tArgs
  t.getAppNumArgs.allM fun i _ =>
    if bis[i]!.isExplicit then
      isExplicitEq tArgs[i]! sArgs[i]!
    else
      isDefEq tArgs[i]! sArgs[i]!

/-- Filter out duplicate rewrites, reflexive rewrites
or rewrites that have metavariables in the replacement expression. -/
@[specialize]
/-
**Mathlib.Tactic.LibraryRewrite.filterRewrites** 是 Mathlib 中的一个定义，位于命名空间 `Mathli
b.Tactic.LibraryRewrite`。
形式化陈述：filterRewrites {α} (e : Expr) (rewrites : Array α) (replacement : α -> Exp
r) (makesNewMVars : α -> Bool) : MetaM (Array α)
参数：e : Expr；rewrites : Array α；replacement : α -> Expr；makesNewMVars : α -> Bool
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Filter out duplicate rewrites, reflexive rewrites
or rewrites that have metavariables in the replacement expression.
-/
def filterRewrites {α} (e : Expr) (rewrites : Array α) (replacement : α → Expr)
    (makesNewMVars : α → Bool) : MetaM (Array α) :=
  withNewMCtxDepth do
  let mut filtered := #[]
  for rw in rewrites do
    -- exclude rewrites that introduce new metavariables into the expression
    if makesNewMVars rw then continue
    -- exclude a reflexive rewrite
    if ← isExplicitEq (replacement rw) e then
      trace[rw??] "discarded reflexive rewrite {replacement rw}"
      continue
    -- exclude two identical looking rewrites
    if ← filtered.anyM (isExplicitEq (replacement rw) <| replacement ·) then
      trace[rw??] "discarded duplicate rewrite {replacement rw}"
      continue
    filtered := filtered.push rw
  return filtered


/-! ### User interface -/


/-- Return syntax for the rewrite tactic `rw [e]`. -/
/-
**Mathlib.Tactic.LibraryRewrite.mkRewrite** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tac
tic.LibraryRewrite`。
形式化陈述：mkRewrite (occ : Option Nat) (symm : Bool) (e : Term) (loc : Option Name) 
: CoreM (TSyntax `tactic)
参数：occ : Option Nat；symm : Bool；e : Term；loc : Option Name。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return syntax for the rewrite tactic `rw [e]`.
-/
def mkRewrite (occ : Option Nat) (symm : Bool) (e : Term) (loc : Option Name) :
    CoreM (TSyntax `tactic) := do
  let loc ← loc.mapM fun h => `(Lean.Parser.Tactic.location| at $(mkIdent h):term)
  let rule ← if symm then `(Parser.Tactic.rwRule| ← $e) else `(Parser.Tactic.rwRule| $e:term)
  match occ with
  | some n => `(tactic| nth_rw $(Syntax.mkNatLit n):num [$rule] $(loc)?)
  | none => `(tactic| rw [$rule] $(loc)?)

/-- Given tactic syntax `tac` that we want to paste into the editor, return it as a string.
This function respects the 100 character limit for long lines. -/
/-
**Mathlib.Tactic.LibraryRewrite.tacticPasteString** 是 Mathlib 中的一个定义，位于命名空间 `Mat
hlib.Tactic.LibraryRewrite`。
形式化陈述：tacticPasteString (tac : TSyntax `tactic) (range : Lsp.Range) : CoreM Stri
ng
参数：tac : TSyntax `tactic；range : Lsp.Range。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given tactic syntax `tac` that we want to paste into the editor, return it as a 
string.
This function respects the 100 character limit for long lines.
-/
def tacticPasteString (tac : TSyntax `tactic) (range : Lsp.Range) : CoreM String := do
  let column := range.start.character
  let indent := column
  return (← PrettyPrinter.ppTactic tac).pretty 100 indent column

/-- Return the rewrite tactic that performs the rewrite. -/
/-
**Mathlib.Tactic.LibraryRewrite.tacticSyntax** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.
Tactic.LibraryRewrite`。
形式化陈述：tacticSyntax (rw : Rewrite) (occ : Option Nat) (loc : Option Name) : MetaM
 (TSyntax `tactic)
参数：rw : Rewrite；occ : Option Nat；loc : Option Name。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return the rewrite tactic that performs the rewrite.
-/
def tacticSyntax (rw : Rewrite) (occ : Option Nat) (loc : Option Name) :
    MetaM (TSyntax `tactic) := withoutModifyingMCtx do
  -- we want the new metavariables to be printed as `?_` in the tactic syntax
  for (mvarId, _) in rw.extraGoals do mvarId.setTag .anonymous
  let proof ← withOptions (pp.mvars.anonymous.set · false) (PrettyPrinter.delab rw.proof)
  mkRewrite occ rw.symm proof loc

open Widget ProofWidgets Jsx Server

/-- The structure with all data necessary for rendering a rewrite suggestion -/
/-
**Mathlib.Tactic.LibraryRewrite.RewriteInterface** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ma
thlib.Tactic.LibraryRewrite`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure with all data necessary for rendering a rewrite suggestion
-/
structure RewriteInterface where
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
  /-- The rewrite tactic string that performs the rewrite -/
  tactic : String
  /-- The replacement expression obtained from the rewrite -/
  replacement : Expr
  /-- The replacement expression obtained from the rewrite -/
  replacementString : String
  /-- The extra goals created by the rewrite -/
  extraGoals : Array CodeWithInfos
  /-- The lemma name with hover information -/
  prettyLemma : CodeWithInfos
  /-- The type of the lemma -/
  lemmaType : Expr
  /-- Whether the rewrite introduces new metavariables with the replacement. -/
  makesNewMVars : Bool

/-- Construct the `RewriteInterface` from a `Rewrite`. -/
/-
**Mathlib.Tactic.LibraryRewrite.Rewrite.toInterface** 是 Mathlib 中的一个定义，位于命名空间 `M
athlib.Tactic.LibraryRewrite.Rewrite`。
形式化陈述：Mathlib.Tactic.LibraryRewrite.Rewrite →   Name ⊕ FVarId → Option ℕ → Optio
n Name → Lsp.Range → MetaM Mathlib.Tactic.LibraryRewrite.RewriteInterface
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the `RewriteInterface` from a `Rewrite`.
-/
def Rewrite.toInterface (rw : Rewrite) (name : Name ⊕ FVarId) (occ : Option Nat)
    (loc : Option Name) (range : Lsp.Range) : MetaM RewriteInterface := do
  let tactic ← tacticSyntax rw occ loc
  let tactic ← tacticPasteString tactic range
  let replacementString := Format.pretty (← ppExpr rw.replacement)
  let mut extraGoals := #[]
  for (mvarId, bi) in rw.extraGoals do
    if bi.isExplicit then
      let extraGoal ← ppExprTagged (← instantiateMVars (← mvarId.getType))
      extraGoals := extraGoals.push extraGoal
  match name with
  | .inl name =>
    let prettyLemma := match ← ppExprTagged (← mkConstWithLevelParams name) with
      | .tag tag _ => .tag tag (.text s!"{name}")
      | code => code
    let lemmaType := (← getConstInfo name).type
    return { rw with tactic, replacementString, extraGoals, prettyLemma, lemmaType }
  | .inr fvarId =>
    let prettyLemma ← ppExprTagged (.fvar fvarId)
    let lemmaType ← fvarId.getType
    return { rw with tactic, replacementString, extraGoals, prettyLemma, lemmaType }

/-- The kind of rewrite -/
/-
**Mathlib.Tactic.LibraryRewrite.Kind** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic
.LibraryRewrite`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kind of rewrite
-/
inductive Kind where
  /-- A rewrite with a local hypothesis -/
  | hypothesis
  /-- A rewrite with a lemma from the current file -/
  | fromFile
  /-- A rewrite with a lemma from an imported file -/
  | fromCache

/-- Return the Interfaces for rewriting `e`, both filtered and unfiltered. -/
/-
**Mathlib.Tactic.LibraryRewrite.getRewriteInterfaces** 是 Mathlib 中的一个定义，位于命名空间 `
Mathlib.Tactic.LibraryRewrite`。
形式化陈述：getRewriteInterfaces (e : Expr) (occ : Option Nat) (loc : Option Name) (ex
cept : Option FVarId) (range : Lsp.Range) : MetaM (Array (Array RewriteInterface
 × Kind) × Array (Array RewriteInterface × Kind))
参数：e : Expr；occ : Option Nat；loc : Option Name；except : Option FVarId；range : Ls
p.Range。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return the Interfaces for rewriting `e`, both filtered and unfiltered.
-/
def getRewriteInterfaces (e : Expr) (occ : Option Nat) (loc : Option Name) (except : Option FVarId)
    (range : Lsp.Range) :
    MetaM (Array (Array RewriteInterface × Kind) × Array (Array RewriteInterface × Kind)) := do
  let mut filtr := #[]
  let mut all := #[]
  for rewrites in ← getHypothesisRewrites e except do
    let rewrites ← rewrites.mapM fun (rw, fvarId) => rw.toInterface (.inr fvarId) occ loc range
    all := all.push (rewrites, .hypothesis)
    filtr := filtr.push (← filterRewrites e rewrites (·.replacement) (·.makesNewMVars), .hypothesis)

  for rewrites in ← getModuleRewrites e do
    let rewrites ← rewrites.mapM fun (rw, name) => rw.toInterface (.inl name) occ loc range
    all := all.push (rewrites, .fromFile)
    filtr := filtr.push (← filterRewrites e rewrites (·.replacement) (·.makesNewMVars), .fromFile)

  for rewrites in ← getImportRewrites e do
    let rewrites ← rewrites.mapM fun (rw, name) => rw.toInterface (.inl name) occ loc range
    all := all.push (rewrites, .fromCache)
    filtr := filtr.push (← filterRewrites e rewrites (·.replacement) (·.makesNewMVars), .fromCache)
  return (filtr, all)

/-- Render the matching side of the rewrite lemma.
This is shown at the header of each section of rewrite results. -/
/-
**Mathlib.Tactic.LibraryRewrite.pattern** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tacti
c.LibraryRewrite`。
形式化陈述：pattern {α} (type : Expr) (symm : Bool) (k : Expr -> MetaM α) : MetaM α
参数：type : Expr；symm : Bool；k : Expr -> MetaM α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Render the matching side of the rewrite lemma.
This is shown at the header of each section of rewrite results.
-/
def pattern {α} (type : Expr) (symm : Bool) (k : Expr → MetaM α) : MetaM α := do
  forallTelescopeReducing type fun _ e => do
    let some (lhs, rhs) := eqOrIff? (← whnf e) | throwError "Expected equation, not {indentExpr e}"
    k (if symm then rhs else lhs)

/-- Render the given rewrite results. -/
/-
**Mathlib.Tactic.LibraryRewrite.renderRewrites** 是 Mathlib 中的一个定义，位于命名空间 `Mathli
b.Tactic.LibraryRewrite`。
形式化陈述：renderRewrites (e : Expr) (results : Array (Array RewriteInterface × Kind)
) (range : Lsp.Range) (doc : FileWorker.EditableDocument) (showNames : Bool) : M
etaM Html
参数：e : Expr；results : Array (Array RewriteInterface × Kind)；range : Lsp.Range；do
c : FileWorker.EditableDocument；showNames : Bool。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Render the given rewrite results.
-/
def renderRewrites (e : Expr) (results : Array (Array RewriteInterface × Kind))
    (range : Lsp.Range) (doc : FileWorker.EditableDocument) (showNames : Bool) :
    MetaM Html := do
  let htmls ← results.filterMapM (renderSection showNames)
  if htmls.isEmpty then
    return <p> No rewrites found for <InteractiveCode fmt={← ppExprTagged e}/> </p>
  else
    return .element "div" #[("style", json% {"marginLeft" : "4px"})] htmls
where
  /-- Render one section of rewrite results. -/
  renderSection (showNames : Bool) (sec : Array RewriteInterface × Kind) : MetaM (Option Html) := do
    let some head := sec.1[0]? | return none
    let suffix := match sec.2 with
      | .hypothesis => " (local hypotheses)"
      | .fromFile => " (lemmas from current file)"
      | .fromCache => ""
    return <details «open»={true}>
      <summary className="mv2 pointer">
        Pattern
        {← pattern head.lemmaType head.symm (return <InteractiveCode fmt={← ppExprTagged ·}/>)}
        {.text suffix}
      </summary>
      {renderSectionCore showNames sec.1}
    </details>

  /-- Render the list of rewrite results in one section. -/
  renderSectionCore (showNames : Bool) (sec : Array RewriteInterface) : Html :=
    .element "ul" #[("style", json% { "padding-left" : "30px"})] <|
    sec.map fun rw =>
      <li> { .element "p" #[] <|
        let button :=
          <span className="font-code"> {
            Html.ofComponent MakeEditLink
              (.ofReplaceRange doc.meta range rw.tactic)
              #[.text rw.replacementString] }
          </span>
        let extraGoals := rw.extraGoals.flatMap fun extraGoal =>
          #[<br/>, <strong className="goal-vdash">⊢ </strong>, <InteractiveCode fmt={extraGoal}/>]
        #[button] ++ extraGoals ++
          if showNames then #[<br/>, <InteractiveCode fmt={rw.prettyLemma}/>] else #[] }
      </li>

/-- The rpc method of the `rw??` widget. -/
@[server_rpc_method]
/-
**Mathlib.Tactic.LibraryRewrite.rpc** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Li
braryRewrite`。
形式化陈述：rpc (props : SelectInsertParams) : RequestM (RequestTask Html)
参数：props : SelectInsertParams。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rpc method of the `rw??` widget.
-/
def rpc (props : SelectInsertParams) : RequestM (RequestTask Html) :=
  RequestM.asTask do
  let doc ← RequestM.readDoc
  let some loc := props.selectedLocations.back? |
    return .text "rw??: Please shift-click an expression."
  if loc.loc matches .hypValue .. then
    return .text "rw??: cannot rewrite in the value of a let variable."
  let some goal := props.goals[0]? | return .text "rw??: there is no goal to solve!"
  if loc.mvarId != goal.mvarId then
    return .text "rw??: the selected expression should be in the main goal."
  goal.ctx.val.runMetaM {} do
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do

      let rootExpr ← loc.rootExpr
      let some (subExpr, occ) ← withReducible <| viewKAbstractSubExpr rootExpr loc.pos |
        return .text "rw??: expressions with bound variables are not yet supported"
      unless ← kabstractIsTypeCorrect rootExpr subExpr loc.pos do
        return .text <| "rw??: the selected expression cannot be rewritten, \
          because the motive is not type correct. \
          This usually occurs when trying to rewrite a term that appears as a dependent argument."
      let location ← loc.fvarId?.mapM FVarId.getUserName

      let (filtered, all) ← getRewriteInterfaces subExpr occ location loc.fvarId? props.replaceRange
      let filtered ← renderRewrites subExpr filtered props.replaceRange doc false
      let all      ← renderRewrites subExpr all      props.replaceRange doc true
      return <FilterDetails
        summary={.text "Rewrite suggestions:"}
        all={all}
        filtered={filtered}
        initiallyFiltered={true} />

/-- The component called by the `rw??` tactic -/
@[widget_module]
/-
**Mathlib.Tactic.LibraryRewrite.LibraryRewriteComponent** 是 Mathlib 中的一个定义，位于命名空
间 `Mathlib.Tactic.LibraryRewrite`。
形式化陈述：LibraryRewriteComponent : Component SelectInsertParams
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The component called by the `rw??` tactic
-/
def LibraryRewriteComponent : Component SelectInsertParams :=
  mk_rpc_widget% LibraryRewrite.rpc

/--
`rw??` is an interactive tactic that suggests rewrites for any expression selected by the user.
To use it, shift-click an expression in the goal or a hypothesis that you want to rewrite.
Clicking on one of the rewrite suggestions will paste the relevant rewrite tactic into the editor.

The rewrite suggestions are grouped and sorted by the pattern that the rewrite lemmas match with.
Rewrites that don't change the goal and rewrites that create the same goal as another rewrite
are filtered out, as well as rewrites that have new metavariables in the replacement expression.
To see all suggestions, click on the filter button (▼) in the top right.
-/
elab stx:"rw??" : tactic => do
  let some range := (← getFileMap).lspRangeOfStx? stx | return
  Widget.savePanelWidgetInfo (hash LibraryRewriteComponent.javascript)
    (pure <| json% { replaceRange : $range }) stx


/-- Represent a `Rewrite` as `MessageData`. -/
/-
**Mathlib.Tactic.LibraryRewrite.Rewrite.toMessageData** 是 Mathlib 中的一个定义，位于命名空间 
`Mathlib.Tactic.LibraryRewrite.Rewrite`。
形式化陈述：Mathlib.Tactic.LibraryRewrite.Rewrite → Name → MetaM MessageData
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Represent a `Rewrite` as `MessageData`.
-/
def Rewrite.toMessageData (rw : Rewrite) (name : Name) : MetaM MessageData := do
  let extraGoals ← rw.extraGoals.filterMapM fun (mvarId, bi) => do
    if bi.isExplicit then
      return some m! "⊢ {← mvarId.getType}"
    return none
  let list := [m! "{rw.replacement}"]
      ++ extraGoals.toList
      ++ [m! "{name}"]
  return .group <| .nest 2 <| "· " ++ .joinSep list "\n"

/-- Represent a section of rewrites as `MessageData`. -/
/-
**Mathlib.Tactic.LibraryRewrite.SectionToMessageData** 是 Mathlib 中的一个定义，位于命名空间 `
Mathlib.Tactic.LibraryRewrite`。
形式化陈述：SectionToMessageData (sec : Array (Rewrite × Name) × Bool) : MetaM (Option
 MessageData)
参数：sec : Array (Rewrite × Name) × Bool。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Represent a section of rewrites as `MessageData`.
-/
def SectionToMessageData (sec : Array (Rewrite × Name) × Bool) : MetaM (Option MessageData) := do
  let rewrites ← sec.1.toList.mapM fun (rw, name) => rw.toMessageData name
  let rewrites : MessageData := .group (.joinSep rewrites "\n")
  let some (rw, name) := sec.1[0]? | return none
  let head ← pattern (← getConstInfo name).type rw.symm (addMessageContext m! "{·}")
  return some <| "Pattern " ++ head ++ "\n" ++ rewrites

/-- `#rw?? e` gives all possible rewrites of `e`. It is a testing command for the `rw??` tactic -/
syntax (name := rw??Command) "#rw??" (&"all")? term : command

open Elab
/-- Elaborate a `#rw??` command. -/
@[command_elab rw??Command]
/-
**Mathlib.Tactic.LibraryRewrite.elabrw** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic
.LibraryRewrite`。
形式化陈述：elabrw??Command : Command.CommandElab
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Elaborate a `#rw??` command.
-/
def elabrw??Command : Command.CommandElab := fun stx =>
  withoutModifyingEnv <| Command.runTermElabM fun _ => do
  let e ← Term.elabTerm stx[2] none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← Term.levelMVarToParam (← instantiateMVars e)

  let filter := stx[1].isNone
  let mut rewrites := #[]
  for rws in ← getModuleRewrites e do
    let rws ← if filter then
      filterRewrites e rws (·.1.replacement) (·.1.makesNewMVars)
      else pure rws
    rewrites := rewrites.push (rws, true)
  for rws in ← getImportRewrites e do
    let rws ← if filter then
      filterRewrites e rws (·.1.replacement) (·.1.makesNewMVars)
      else pure rws
    rewrites := rewrites.push (rws, false)

  let sections ← liftMetaM <| rewrites.filterMapM SectionToMessageData
  if sections.isEmpty then
    logInfo m! "No rewrites found for {e}"
  else
    logInfo (.joinSep sections.toList "\n\n")

end Mathlib.Tactic.LibraryRewrite

