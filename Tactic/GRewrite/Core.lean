/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Sebastian Zimmer, Mario Carneiro, Heather Macbeth
-/
module

public meta import Lean.Meta.Tactic.Rewrite
public import Mathlib.Tactic.GCongr.Core

/-!
# The generalized rewriting tactic

This module defines the core of the `grw`/`grewrite` tactic.

This file provides two implementations of the tactic:
1. The simple implementation uses `kabstract` to determine where to rewrite,
   and then calls `MVarId.gcongr` to prove that the rewrite is valid.
   This is used by `nth_grw` and `grw +useKAbstract`.
2. The more sophisticated implementation has its own congruence loop, applying `gcongr` lemmas to
   create the replacement expression, and to prove that this is related to the original expression.
   This supports the use of strict inequalities to change the strictness in the goal.
   This is used by `grw` and `apply_rw`.
-/

meta section

namespace Mathlib.Tactic.GRewrite

open Lean Meta GCongr

/-- The result returned by `Lean.MVarId.grewrite`. -/
public structure GRewriteResult where
  /-- The rewritten expression -/
  eNew : Expr
  /-- The proof of the implication. The direction depends on the argument `forwardImp`. -/
  impProof : Expr
  /-- The new side goals -/
  mvarIds : List MVarId -- new goals
  /-- The outermost local context in which the rewrite makes sense. If the rewrite does not involve
  bound variables, this is `none`. This is used for fixing the generated info tree, so that the
  "Expected Type" is displayed correctly. -/
  lctx? : Option LocalContext

/-- Configures the behavior of the `rewrite` and `rw` tactics. -/
public structure Config extends Rewrite.Config where
  /-- When `useRewrite = true`, switch to using the default `rewrite` tactic when the goal is
  and equality or iff. -/
  useRewrite : Bool := true
  /-- When `implicationHyp = true`, interpret the rewrite rule as an implication. -/
  implicationHyp : Bool := false
  /-- Whether to use `kabstract` to find the rewrites locations. -/
  useKAbstract := false

section kabstract

/--
Definition of `dischargeMain` / `dischargeMain` 的定义

English:
definition dischargeMain
  signature: (hrel : Expr) (goal : MVarId)
  body: do
  if ← goal.gcongrForward #[hrel] then
    return true
  else
    throwTacticEx `grewrite goal m!"could not discharge {← goal.getType} using {← inferType hrel}"

中文:
定义 dischargeMain
  签名: (hrel : Expr) (goal : MVarId)
  定义体: do
  if ← goal.gcongrForward #[hrel] then
    return true
  else
    throwTacticEx `grewrite goal m!"could not discharge {← goal.getType} using {← inferType hrel}"
-/
def dischargeMain (hrel : Expr) (goal : MVarId) : MetaM Bool := do
  if ← goal.gcongrForward #[hrel] then
    return true
  else
    throwTacticEx `grewrite goal m!"could not discharge {← goal.getType} using {← inferType hrel}"

/--
Definition of `grewriteUsingKAbstract` / `grewriteUsingKAbstract` 的定义

English:
definition grewriteUsingKAbstract
  signature: (goal : MVarId) (e hrel pattern replacement : Expr)
  body: do
let eAbst ← withConfig (fun oldConfig => { config, oldConfig with })
    kabstract e pattern config.occs
  unless eAbst.hasLooseBVars do
    throwTacticEx `grewrite goal
      m!"did not find instance of the pattern in the target expression{indentExpr pattern}"
  -- construct `eNew` by instantiat

中文:
定义 grewriteUsingKAbstract
  签名: (goal : MVarId) (e hrel pattern replacement : Expr)
  定义体: do
let eAbst ← withConfig (fun oldConfig => { config, oldConfig with })
    kabstract e pattern config.occs
  unless eAbst.hasLooseBVars do
    throwTacticEx `grewrite goal
      m!"did not find instance of the pattern in the target expression{indentExpr pattern}"
  -- construct `eNew` by instantiat
-/
def grewriteUsingKAbstract (goal : MVarId) (e hrel pattern replacement : Expr)
    (forwardImp : Bool) (config : GRewrite.Config) : MetaM (Expr × Expr × Array MVarId) := do
let eAbst ← withConfig (fun oldConfig => { config, oldConfig with })
    kabstract e pattern config.occs
  unless eAbst.hasLooseBVars do
    throwTacticEx `grewrite goal
      m!"did not find instance of the pattern in the target expression{indentExpr pattern}"
  -- construct `eNew` by instantiating `eAbst` with `replacement`.
  let eNew := eAbst.instantiate1 replacement
  let eNew ← instantiateMVars eNew
  -- check that `eNew` is well typed
  try
    check eNew
  catch ex =>
    throwTacticEx `grewrite goal m!"\
      rewritten expression is not type correct:{indentD eNew}\nError: {ex.toMessageData}\
      \n\n\
      Possible solutions: use grewrite's 'occs' configuration option \
      to limit which occurrences are rewritten, \
      or specify what the rewritten expression should be and use 'gcongr'."
  let eNew ← if replacement.hasBinderNameHint then eNew.resolveBinderNameHint else pure eNew
  -- Construct the implication proof using `gcongr`.
  -- Although `e` and `e'` are defEq, they may not be defEq in the `reducible` transparency.
  -- So, it is important to use `e'` in the `gcongr` goal.
  let e' := eAbst.instantiate1 (GCongr.mkHoleAnnotation pattern)
  let mkImp (e₁ e₂ : Expr) : Expr := .forallE `_a e₁ e₂ .default
  let imp := if forwardImp then mkImp e' eNew else mkImp eNew e'
  let gcongrGoal ← mkFreshExprMVar imp
  let (_, sideGoals) ← gcongrGoal.mvarId!.gcongr forwardImp
.run (mainGoalDischarger := GRewrite.dischargeMain hrel)
  pure (eNew, gcongrGoal, sideGoals)

end kabstract

section singlePass

initialize registerTraceClass `Meta.grewrite

/--
Inductive type `Progress` / 归纳类型 `Progress`

English:
inductive Progress
  parameters: where
  constructors (3):
    - noMatch: 
    - matched: 
    - matchedOutOfScope: (lctx : LocalContext)

中文:
归纳类型 Progress
  参数: where
  构造子 (3 个):
    - noMatch: 
    - matched: 
    - matchedOutOfScope: (lctx : LocalContext)
-/
inductive Progress where
  /-- The rewrite lemma has not unified with anything yet. -/
  | noMatch
  /-- The rewrite lemma has unified with something. -/
  | matched
  /-- The rewrite lemma has unified with something, and depends on a free variable that is now
  out of scope. We store a local context in which the rewrite makes sense. -/
  | matchedOutOfScope (lctx : LocalContext)

/--
Definition of `State` / `State` 的定义

English:
structure State
  parameters: where
  axioms and operations (2):
    - cache : Std.HashSet (Option Expr × Expr × Bool)  [default: {}]
    - progress : Progress  [default: .noMatch]

中文:
结构 State
  参数: where
  公理与运算 (2 个):
    - cache : Std.HashSet (选项类型 Expr × Expr × 布尔值)  [默认: {}]
    - progress : Progress  [默认: .noMatch]
-/
structure State where
  /-- The cache used in `grw` to avoid trying and failing to rewrite the same term multiple times.
  Each key stores the relation (`none` encodes the `→` relation), rewritten expression,
  and direction of the rewrite.
  This lets us avoid an exponential blowup when there are multiple `gcongr` lemmas for rewriting
  in the same place, such as `add_le_add`, `add_le_add_left` and `add_le_add_right`. -/
  cache : Std.HashSet (Option Expr × Expr × Bool) := {}
  /-- The current progress level. -/
  progress : Progress := .noMatch

/--
Definition of `GRewriteLemma` / `GRewriteLemma` 的定义

English:
structure GRewriteLemma
  parameters: where
  axioms and operations (5):
    - symm : Bool
    - proof : Expr
    - type : Expr
    - index : HeadIndex × Nat
    - mvarIds : Array (MVarId × Array LocalDecl)

中文:
结构 GRewriteLemma
  参数: where
  公理与运算 (5 个):
    - symm : 布尔值
    - proof : Expr
    - type : Expr
    - index : HeadIndex × 自然数
    - mvarIds : 数组 (MVarId × 数组 LocalDecl)
-/
structure GRewriteLemma where
  /-- Whether the lemma rewrites right-to-left (i.e. whether it has a `←`). -/
  symm : Bool
  /-- The value -/
  proof : Expr
  /-- The type -/
  type : Expr
  /-- The key used to determine where to attempt rewriting. -/
  index : HeadIndex × Nat
  /-- The metavariables that appear in the lemma. We do the slightly dodgy thing of
  modifying their local context in order to be able to unify with bound variables. -/
  mvarIds : Array (MVarId × Array LocalDecl)

/--
Definition of `GRewriteM` / `GRewriteM` 的定义

English:
abbreviation GRewriteM
  body: ReaderT GRewriteLemma StateRefT State GCongr.GCongrM

中文:
缩写 GRewriteM
  定义体: ReaderT GRewriteLemma StateRefT State GCongr.GCongrM

Depends on / 依赖: GCongr, GCongr.GCongrM, GCongrM, GRewriteLemma, ReaderT, StateRefT
-/
abbrev GRewriteM := ReaderT GRewriteLemma StateRefT State GCongr.GCongrM

/--
Definition of `GRewriteLemma.apply` / `GRewriteLemma.apply` 的定义

English:
definition GRewriteLemma.apply
  signature: (lem : GRewriteLemma) (goal : MVarId) (symm : Bool)
  body: do
  withTraceNode `Meta.grewrite (fun _ => return m!"rewriting with `{lem.proof}`") do
  let (type, proof) ←
    if symm then
      let proof ← try lem.proof.applySymm catch _ => return false
      pure (← inferType proof, proof)
    else
      pure (lem.type, lem.proof)
  withConfig (fun oldConfig

中文:
定义 GRewriteLemma.apply
  签名: (lem : GRewriteLemma) (goal : MVarId) (symm : 布尔值)
  定义体: do
  withTraceNode `Meta.grewrite (fun _ => return m!"rewriting with `{lem.proof}`") do
  let (type, proof) ←
    if symm then
      let proof ← try lem.proof.applySymm catch _ => return false
      pure (← inferType proof, proof)
    else
      pure (lem.type, lem.proof)
  withConfig (fun oldConfig
-/
def GRewriteLemma.apply (lem : GRewriteLemma) (goal : MVarId) (symm : Bool)
    (config : GRewrite.Config) : MetaM Bool := do
  withTraceNode `Meta.grewrite (fun _ => return m!"rewriting with `{lem.proof}`") do
  let (type, proof) ←
    if symm then
      let proof ← try lem.proof.applySymm catch _ => return false
      pure (← inferType proof, proof)
    else
      pure (lem.type, lem.proof)
  withConfig (fun oldConfig => { config, oldConfig with }) do
  if ← isDefEq (← goal.getType) type then
    goal.assign proof
    return true
  let mctx ← getMCtx
  for (n, tac) in (forwardExt.getState (← getEnv)).2 do
    -- Explicitly exclude a few `gcongr_forward` extensions that are not relevant here.
    if n matches ``GCongr.exact | ``GCongr.exactRefl then continue
    try tac.eval proof goal; return true
    catch _ => setMCtx mctx
  return false

/--
Definition of `makeGCongrGoal` / `makeGCongrGoal` 的定义

English:
definition makeGCongrGoal
  signature: (rel? : Option Expr) (e : Expr) (forward : Bool)
  body: do
  if let some rel := rel? then
    let .forallE _ d₁ (.forallE _ d₂ _ _) _ ← whnf (← inferType rel) | throwFunctionExpected rel
    -- note that `@[gcongr]`'s checks should prevent this happening
    if d₂.hasLooseBVars then throwError "grw: {rel} is a dependent relation"
    if forward then
    

中文:
定义 makeGCongrGoal
  签名: (rel? : 选项类型 Expr) (e : Expr) (forward : 布尔值)
  定义体: do
  if let some rel := rel? then
    let .forallE _ d₁ (.forallE _ d₂ _ _) _ ← whnf (← inferType rel) | throwFunctionExpected rel
    -- note that `@[gcongr]`'s checks should prevent this happening
    if d₂.hasLooseBVars then throwError "grw: {rel} is a dependent relation"
    if forward then
    
-/
def makeGCongrGoal (rel? : Option Expr) (e : Expr) (forward : Bool) : MetaM (Expr × Expr) := do
  if let some rel := rel? then
    let .forallE _ d₁ (.forallE _ d₂ _ _) _ ← whnf (← inferType rel) | throwFunctionExpected rel
    -- note that `@[gcongr]`'s checks should prevent this happening
    if d₂.hasLooseBVars then throwError "grw: {rel} is a dependent relation"
    if forward then
      let mvar ← mkFreshExprMVar d₂
      return (mvar, ← mkFreshExprMVar <| mkApp2 rel e mvar)
    else
      let mvar ← mkFreshExprMVar d₁
      return (mvar, ← mkFreshExprMVar <| mkApp2 rel mvar e)
  else
    let mvar ← mkFreshTypeMVar
    let target := if forward then .forallE `_a e mvar .default else .forallE `_a mvar e .default
    return (mvar, ← mkFreshExprMVar (some target))

/--
Definition of `getRel'` / `getRel'` 的定义

English:
definition getRel'
  signature: (e : Expr)
  body: match e with
  | .app (.app rel lhs) rhs => rel.getAppFn.constName?.map (·, rel, lhs, rhs)
  | .forallE _ lhs rhs _ =>
    if !rhs.hasLooseBVars then
      some (`_Implies, none, lhs, rhs)
    else
      none
  | _ => none

mutual

中文:
定义 getRel'
  签名: (e : Expr)
  定义体: match e with
  | .app (.app rel lhs) rhs => rel.getAppFn.constName?.map (·, rel, lhs, rhs)
  | .forallE _ lhs rhs _ =>
    if !rhs.hasLooseBVars then
      some (`_Implies, none, lhs, rhs)
    else
      none
  | _ => none

mutual

Depends on / 依赖: _Implies, constName, forallE, getAppFn, hasLooseBVars, rel.getAppFn.constName, rhs.hasLooseBVars
-/
def getRel' (e : Expr) : Option (Name × Option Expr × Expr × Expr) :=
  match e with
  | .app (.app rel lhs) rhs => rel.getAppFn.constName?.map (·, rel, lhs, rhs)
  | .forallE _ lhs rhs _ =>
    if !rhs.hasLooseBVars then
      some (`_Implies, none, lhs, rhs)
    else
      none
  | _ => none

mutual

/--
Definition of `processGCongrHypothesisAux` / `processGCongrHypothesisAux` 的定义

English:
definition processGCongrHypothesisAux
  signature: (goal : MVarId) (forward : Bool) (config : Config)
  body: do
  let some (relName, rel?, lhs, rhs) := getRel' (← whnf (← goal.getType)) |
    throwError "internal `grewrite` error: invalid `gcongr` goal {goal}"
  let (target, mvarApp) := if forward then (lhs, rhs) else (rhs, lhs)
  if let some (result, proof) ← grewriteCore relName rel? target forward confi

中文:
定义 processGCongrHypothesisAux
  签名: (goal : MVarId) (forward : 布尔值) (config : 余nfig)
  定义体: do
  let some (relName, rel?, lhs, rhs) := getRel' (← whnf (← goal.getType)) |
    throwError "internal `grewrite` error: invalid `gcongr` goal {goal}"
  let (target, mvarApp) := if forward then (lhs, rhs) else (rhs, lhs)
  if let some (result, proof) ← grewriteCore relName rel? target forward confi
-/
partial def processGCongrHypothesisAux (goal : MVarId) (forward : Bool) (config : Config) :
    GRewriteM Bool := do
  let some (relName, rel?, lhs, rhs) := getRel' (← whnf (← goal.getType)) |
    throwError "internal `grewrite` error: invalid `gcongr` goal {goal}"
  let (target, mvarApp) := if forward then (lhs, rhs) else (rhs, lhs)
  if let some (result, proof) ← grewriteCore relName rel? target forward config then
    mvarApp.withApp fun mvar xs => do
      /- Note: the names of the free variables `xs` end up in the new goal as lambda binders.
      `applyGCongrLemma` ensures that these are the binder names that appear in the original goal.
      As a result, when rewriting inside of `{x | p x}`, the binder name `x` is preserved. -/
      mvar.mvarId!.assign (← mkLambdaFVars xs result)
      goal.assign proof
      return true
  else
    return false

/--
Definition of `processGCongrHypothesis` / `processGCongrHypothesis` 的定义

English:
definition processGCongrHypothesis
  signature: (goal : MVarId) (forward : Bool)
  body: do
  -- If the local context was not changed, we don't need to modify the local contexts.
  if (← goal.getDecl).lctx.numIndices == (← getLCtx).numIndices then
    processGCongrHypothesisAux goal forward config
  else
  let outerLCtx ← getLCtx
  goal.withContext do
  -- We can only modify the metavar

中文:
定义 processGCongrHypothesis
  签名: (goal : MVarId) (forward : 布尔值)
  定义体: do
  -- If the local context was not changed, we don't need to modify the local contexts.
  if (← goal.getDecl).lctx.numIndices == (← getLCtx).numIndices then
    processGCongrHypothesisAux goal forward config
  else
  let outerLCtx ← getLCtx
  goal.withContext do
  -- We can only modify the metavar
-/
partial def processGCongrHypothesis (goal : MVarId) (forward : Bool)
    (config : Config) : GRewriteM Bool := do
  -- If the local context was not changed, we don't need to modify the local contexts.
  if (← goal.getDecl).lctx.numIndices == (← getLCtx).numIndices then
    processGCongrHypothesisAux goal forward config
  else
  let outerLCtx ← getLCtx
  goal.withContext do
  -- We can only modify the metavariable local contexts if no match has happened yet.
  if (← get).progress matches .noMatch then
    let mctx ← getMCtx
    let lctx ← getLCtx
setMCtx (← read).mvarIds.foldl (init := mctx) fun mctx (mvarId, decls) =>
      -- Create a local context for `mvarId` by adding `decls` to the current local context.
      let lctx := decls.foldl (·.addDecl ·) lctx
      { mctx with decls := mctx.decls.insert mvarId { mctx.getDecl mvarId with lctx } }
    let result ← processGCongrHypothesisAux goal forward config
    if (← get).progress matches .noMatch then
      -- If we still don't have a match, then revert the changes to the metavariable local contexts.
      setMCtx mctx
    else
      -- If we did get a match, then we might be exiting the scope where this rewrite makes sense,
      -- in which case we should not rewrite any more.
      let validInOuterLCtx ← (← read).mvarIds.allM fun (mvarId, _) => do
        let some val ← getExprMVarAssignment? mvarId | return false
        return (Lean.collectFVars {} val).fvarIds.all outerLCtx.contains
      unless validInOuterLCtx do
        modify ({ · with progress := .matchedOutOfScope (← getLCtx) })
    return result
  else
    processGCongrHypothesisAux goal forward config

/--
Definition of `processGCongrLemma` / `processGCongrLemma` 的定义

English:
definition processGCongrLemma
  signature: (goal : MVarId) (lem : GCongrLemma) (forward : Bool)
  body: withTraceNode `Meta.grewrite (fun _ =>
    return m!"applying `gcongr` lemma {.ofConstName lem.declName}") do
  let (mainGoals, sideGoals) ← try applyGCongrLemma goal lem catch _ => return false
  -- Recursively rewrite in the main subgoals
  let mut anyProgress := false
  for (goal, isContra) in ma

中文:
定义 processGCongrLemma
  签名: (goal : MVarId) (lem : GCongrLemma) (forward : 布尔值)
  定义体: withTraceNode `Meta.grewrite (fun _ =>
    return m!"applying `gcongr` lemma {.ofConstName lem.declName}") do
  let (mainGoals, sideGoals) ← try applyGCongrLemma goal lem catch _ => return false
  -- Recursively rewrite in the main subgoals
  let mut anyProgress := false
  for (goal, isContra) in ma
-/
partial def processGCongrLemma (goal : MVarId) (lem : GCongrLemma) (forward : Bool)
    (config : Config) : GRewriteM Bool :=
  withTraceNode `Meta.grewrite (fun _ =>
    return m!"applying `gcongr` lemma {.ofConstName lem.declName}") do
  let (mainGoals, sideGoals) ← try applyGCongrLemma goal lem catch _ => return false
  -- Recursively rewrite in the main subgoals
  let mut anyProgress := false
  for (goal, isContra) in mainGoals do
    -- Any of the rewrites in this loop could make a match that is out of scope here.
    -- In that case we should stop rewriting, and the remaining goals should be closed `by rfl`.
    unless (← get).progress matches .matchedOutOfScope _ do
      if ← processGCongrHypothesis goal (forward != isContra) config then
        anyProgress := true
        continue
    try
      -- Due to an issue in `rfl`, we need this transparency bump. See https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.60with_reducible.20rfl.60.20failing/with/590957602
      withReducibleAndInstances goal.applyRflOrId
    catch ex =>
      -- In principle, this case should not happen.
      trace[Meta.grewrite] "{← goal.getType} could not be closed with `rfl`:\n{ex.toMessageData}"
      return false
  -- Only continue if at least one rewrite happened
  unless anyProgress do return false
  -- Finally, run the discharger on the side goals.
  for mvarId in sideGoals do
    let type ← mvarId.getType
    -- There may be instance side goals that still had metavariables before recursively rewriting.
    if (← isClass? type).isSome then
      if let some inst ← synthInstance? type then
        mvarId.assign inst
        continue
    else
      dischargeSide mvarId
  return true

/--
Definition of `grewriteCore` / `grewriteCore` 的定义

English:
definition grewriteCore
  signature: (relName : Name) (rel? : Option Expr) (e : Expr) (forward : Bool)
  body: withTraceNodeBefore `Meta.grewrite (fun _ => return m!"visiting `{e}` in the \
    {if forward then "LHS" else "RHS"} of relation `{rel?.elim m!"->" (m!"{·}")}`") do
  let e ← instantiateMVars e; let rel? ← rel?.mapM instantiateMVars
  let cacheKey := (rel?, e, forward)
  if (← get).cache.contains c

中文:
定义 grewriteCore
  签名: (relName : Name) (rel? : 选项类型 Expr) (e : Expr) (forward : 布尔值)
  定义体: withTraceNodeBefore `Meta.grewrite (fun _ => return m!"visiting `{e}` in the \
    {if forward then "LHS" else "RHS"} of relation `{rel?.elim m!"->" (m!"{·}")}`") do
  let e ← instantiateMVars e; let rel? ← rel?.mapM instantiateMVars
  let cacheKey := (rel?, e, forward)
  if (← get).cache.contains c
-/
partial def grewriteCore (relName : Name) (rel? : Option Expr) (e : Expr) (forward : Bool)
    (config : Config) : GRewriteM (Option (Expr × Expr)) :=
  withTraceNodeBefore `Meta.grewrite (fun _ => return m!"visiting `{e}` in the \
    {if forward then "LHS" else "RHS"} of relation `{rel?.elim m!"->" (m!"{·}")}`") do
  let e ← instantiateMVars e; let rel? ← rel?.mapM instantiateMVars
  let cacheKey := (rel?, e, forward)
  if (← get).cache.contains cacheKey then
    trace[Meta.grewrite] "cached: no rewrite"
    return none
  let (mvar, goal) ← makeGCongrGoal rel? e forward
  -- Try the given grewrite lemma.
  let lem ← read
  if (e.toHeadIndex, e.headNumArgs) == lem.index then
    if ← lem.apply goal.mvarId! (forward == lem.symm) config then
      modify ({ · with progress := .matched })
      return (mvar, goal)
  -- Try all applicable `@[gcongr]` lemmas.
  if let some (head, args) := getCongrAppFnArgs e then
    let mut lemmas ← findGCongrLemmas?' relName head forward args.size
    if relName == `_Implies then
      lemmas := lemmas ++ relImpRelLemma args.size
    let mctx ← getMCtx
    for gcongrLem in lemmas do
      if gcongrLem.forGrw then
        if ← processGCongrLemma goal.mvarId! gcongrLem forward config then
          -- Preserve the binder name/info in a forall.
          match e, ← instantiateMVars mvar with
          | .forallE n _ _ bi, .forallE _ d b _ => return some (.forallE n d b bi, goal)
          | _, result => return some (result, goal)
        setMCtx mctx
  -- Cache the fact that there was nothing to rewrite.
  modify fun s => { s with cache := s.cache.insert cacheKey }
  return none

end

end singlePass

/--
Rewrite `e` using the relation `hrel : x ~ y`, and construct an implication proof
using the `gcongr` tactic to discharge this goal.

if `forwardImp = true`, we prove that `e → eNew`; otherwise `eNew → e`.

If `symm = false`, we rewrite `e` to `eNew := e[x/y]`; otherwise `eNew := e[y/x]`.

The code aligns with `Lean.MVarId.rewrite` as much as possible.
-/
public def _root_.Lean.MVarId.grewrite (goal : MVarId) (e : Expr) (hrel : Expr)
    (mvarIds : Array (MVarId × Array LocalDecl)) (forwardImp symm : Bool)
    (config : GRewrite.Config) : MetaM GRewriteResult :=
  goal.withContext do
    goal.checkNotAssigned `grewrite
    let hrelType ← instantiateMVars (← inferType hrel)
    let maxMVars? ←
      if config.implicationHyp then
        if let arity + 1 := hrelType.getForallArity then
          pure (some arity)
        else
          throwTacticEx `apply_rw goal m!"invalid implication {hrelType}"
      else
        pure none
    let (newMVars, binderInfos, hrelType) ←
withReducible forallMetaTelescopeReducing hrelType maxMVars?
    /- We don't reduce `hrelType` because if it is `a > b`, turning it into `b < a` would
    reverse the direction of the rewrite. However, we do need to clear metadata annotations. -/
    let hrelType := hrelType.cleanupAnnotations

    -- If we can use the normal `rewrite` tactic, we default to using that.
    if (hrelType.isAppOfArity ``Iff 2 || hrelType.isAppOfArity ``Eq 3) && config.useRewrite then
      let { eNew, eqProof, mvarIds } ← goal.rewrite e hrel symm config.toConfig
      let mp := if forwardImp then ``Eq.mp else ``Eq.mpr
      let impProof ← mkAppOptM mp #[e, eNew, eqProof]
      return { eNew, impProof, mvarIds, lctx? := none }

    let hrelIn := hrel
    -- check that `hrel` proves a relation
    let hrel := mkAppN hrel newMVars
    let some (_, lhs, rhs) := GCongr.getRel hrelType |
      throwTacticEx `grewrite goal m!"{hrelType} is not a relation"
    let (pattern, replacement) := if symm then (rhs, lhs) else (lhs, rhs)
    if pattern.getAppFn.isMVar then
      throwTacticEx `grewrite goal
        m!"pattern is a metavariable{indentExpr pattern}\nfrom relation{indentExpr hrelType}"
    -- abstract the occurrences of `lhs` from `e` to get `eAbst`
    let e ← instantiateMVars e
    let (lctx?, eNew, impProof, sideGoals) ←
      if config.useKAbstract then
(none, ·) < > grewriteUsingKAbstract goal e hrel pattern replacement forwardImp config
      else
      withReducible do
      let some (_, lhs', rhs') := GCongr.getRel (← whnf hrelType) |
        throwTacticEx `grewrite goal m!"{hrelType} is not a valid relation"
      -- Support relations that flip their arguments when reduced, such as `≥`.
      let symm' ←
        if lhs' == lhs && rhs' == rhs then pure symm
        else if lhs' == rhs && rhs' == lhs then pure !symm
        else throwTacticEx `grewrite goal m!"{hrelType} is not a valid relation"
      let index := (pattern.toHeadIndex, pattern.headNumArgs)
      let mvarIds := mvarIds ++ newMVars.map (·.mvarId!, #[])
      if let ((some (eNew, impProof), { progress, ..}), newGoals) ←
.run grewriteCore `_Implies none e (forward := forwardImp) config
          { symm := symm', proof := hrel, type := hrelType, index, mvarIds }
.run then .run {}
        let lctx? := match progress with
          | .matchedOutOfScope lctx => some lctx
          | _ => none
        pure (lctx?, eNew, impProof, newGoals)
      else
        withLocalDeclD `_ (← inferType replacement) fun replacement' => do
          let hrelType := updateRel hrelType replacement' symm
          throwTacticEx `grewrite goal
            m!"Did not find a rewrite with{indentExpr hrelType}\n\
            in the target expression{indentExpr e}\n\n\
            Use the command `set_option trace.Meta.grewrite true` to inspect this."
    -- post-process the metavariables
    postprocessAppMVars `grewrite goal newMVars binderInfos
      (synthAssignedInstances := !tactic.skipAssignedInstances.get (← getOptions))
    let newMVarIds ← (sideGoals ++ newMVars.map Expr.mvarId!).filterM (not <$> ·.isAssigned)
    let otherMVarIds ← getMVarsNoDelayed hrelIn
    let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
    let newMVarIds := newMVarIds ++ otherMVarIds
    pure { eNew, impProof, mvarIds := newMVarIds.toList, lctx? }

end Mathlib.Tactic.GRewrite
