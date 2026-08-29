/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.Rewrite
public import Mathlib.Tactic.ClickSuggestions.GRewrite
public import Mathlib.Tactic.ClickSuggestions.Apply
public import Mathlib.Tactic.ClickSuggestions.ApplyAt
public meta import Mathlib.Lean.FoldEnvironment
public meta import Mathlib.Lean.Meta.RefinedDiscrTree

/-!
# Generating a shortlist of candidate lemmas for suggestions

## Discrimination tree lookup

This file defines how to build and match with the discrimination trees, for premises that are
- imported
- from the current module
- local hypotheses

## Performance note

When importing all of mathlib, building the discrimination trees takes on the order of 10-15
seconds. This is because of two distinct performance bottlenecks:

1. Looping through the environment, and computing all of the discrimination tree entries is
  expensive, and is done in parallel to speed it up.
2. Building the final discrimination tree by inserting all of the computed entries is less
  expensive, but it cannot be done in parallel, because a single datastructure is being built.

These two bottlenecks cost about the same amount of time. Luckily, we can already start doing (2)
as soon as any of the parallel tasks from (1) have finished. So, we build the discrimination tree
(on the main thread) at the same time that the entries are being computed on various parallel
threads.
-/

meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta RefinedDiscrTree

/--
Definition of `isMVarSwap` / `isMVarSwap` 的定义

English:
definition isMVarSwap
  signature: (t s : Expr)
  body: .isSome go t s {}

中文:
定义 isMVarSwap
  签名: (t s : Expr)
  定义体: .isSome go t s {}

Depends on / 依赖: isSome
-/
def isMVarSwap (t s : Expr) : Bool :=
.isSome go t s {}
where
  /-- The main loop of `isMVarSwap`. Returning `none` corresponds to a failure. -/
  go (t s : Expr) (swaps : List (MVarId × MVarId)) : Option (List (MVarId × MVarId)) := do
  let isTricky e := e.hasExprMVar || e.hasLevelParam
  if isTricky t then
    guard (isTricky s)
    match t, s with
    -- Note we don't bother keeping track of universe level metavariables.
    | .const n₁ _ , .const n₂ _ => guard (n₁ == n₂); some swaps
    | .sort _ , .sort _ => some swaps
    | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => go d₁ d₂ swaps >>= go b₁ b₂
    | .lam _ d₁ b₁ _ , .lam _ d₂ b₂ _ => go d₁ d₂ swaps >>= go b₁ b₂
    | .mdata d₁ e₁ , .mdata d₂ e₂ => guard (d₁ == d₂); go e₁ e₂ swaps
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => go t₁ t₂ swaps >>= go v₁ v₂ >>= go b₁ b₂
    | .app f₁ a₁ , .app f₂ a₂ => go f₁ f₂ swaps >>= go a₁ a₂
    | .proj n₁ i₁ e₁ , .proj n₂ i₂ e₂ => guard (n₁ == n₂ && i₁ == i₂); go e₁ e₂ swaps
    | .fvar fvarId₁ , .fvar fvarId₂ => guard (fvarId₁ == fvarId₂); some swaps
    | .lit v₁ , .lit v₂ => guard (v₁ == v₂); some swaps
    | .bvar i₁ , .bvar i₂ => guard (i₁ == i₂); some swaps
    | .mvar mvarId₁ , .mvar mvarId₂ =>
      match swaps.find? (·.1 == mvarId₁) with
      | none =>
        guard (swaps.all (·.2 != mvarId₂))
        let swaps := (mvarId₁, mvarId₂) :: swaps
        if mvarId₁ == mvarId₂ then
          some swaps
        else
some (mvarId₂, mvarId₁) :: swaps
      | some (_, mvarId) => guard (mvarId == mvarId₂); some swaps
    | _ , _ => none
  else
    guard (t == s); some swaps

/--
Definition of `Entries` / `Entries` 的定义

English:
structure Entries
  parameters: where
  axioms and operations (4):
    - rw : Array (Key × LazyEntry × RwLemma)  [default: #[]]
    - grw : Array (Key × LazyEntry × GrwLemma)  [default: #[]]
    - app : Array (Key × LazyEntry × ApplyLemma)  [default: #[]]
    - appAt : Array (Key × LazyEntry × ApplyAtLemma)  [default: #[]]

中文:
结构 Entries
  参数: where
  公理与运算 (4 个):
    - rw : Array (Key × LazyEntry × RwLemma)  [默认: #[]]
    - grw : Array (Key × LazyEntry × GrwLemma)  [默认: #[]]
    - app : Array (Key × LazyEntry × ApplyLemma)  [默认: #[]]
    - appAt : Array (Key × LazyEntry × ApplyAtLemma)  [默认: #[]]
-/
structure Entries where
  /-- Entries for the `rw` discrimination tree. -/
  rw : Array (Key × LazyEntry × RwLemma) := #[]
  /-- Entries for the `grw` discrimination tree. -/
  grw : Array (Key × LazyEntry × GrwLemma) := #[]
  /-- Entries for the `apply` discrimination tree. -/
  app : Array (Key × LazyEntry × ApplyLemma) := #[]
  /-- Entries for the `apply at` discrimination tree. -/
  appAt : Array (Key × LazyEntry × ApplyAtLemma) := #[]

/-- Push the discrimination tree entry `key => a` onto the array. -/
@[inline]
/--
Definition of `pushEntry` / `pushEntry` 的定义

English:
definition pushEntry
  signature: {α} (arr : Array (Key × LazyEntry × α)) (key : Expr) (a : α)
  body: do
  let entries ← initializeLazyEntryWithEta key
  return entries.foldl (init := arr) fun arr (key, lazy) => arr.push (key, lazy, a)

中文:
定义 pushEntry
  签名: {α} (arr : Array (Key × LazyEntry × α)) (key : Expr) (a : α)
  定义体: do
  let entries ← initializeLazyEntryWithEta key
  return entries.foldl (init := arr) fun arr (key, lazy) => arr.push (key, lazy, a)
-/
def pushEntry {α} (arr : Array (Key × LazyEntry × α)) (key : Expr) (a : α) :
    MetaM (Array (Key × LazyEntry × α)) := do
  let entries ← initializeLazyEntryWithEta key
  return entries.foldl (init := arr) fun arr (key, lazy) => arr.push (key, lazy, a)

/--
Definition of `isBadMatch` / `isBadMatch` 的定义

English:
definition isBadMatch
  signature: (e : Expr)
  body: e.getAppFn.isMVar ||
  -- This extra check excludes lemmas that match a general equality
  -- these are almost never useful, and there are very many of them.
  -- We could consider removing this check.
  e.eq?.any fun (α, l, r) =>
    α.getAppFn.isMVar && l.getAppFn.isMVar && r.getAppFn.isMVar && l 

中文:
定义 isBadMatch
  签名: (e : Expr)
  定义体: e.getAppFn.isMVar ||
  -- This extra check excludes lemmas that match a general equality
  -- these are almost never useful, and there are very many of them.
  -- We could consider removing this check.
  e.eq?.any fun (α, l, r) =>
    α.getAppFn.isMVar && l.getAppFn.isMVar && r.getAppFn.isMVar && l 

Depends on / 依赖: e.getAppFn.isMVar, getAppFn, isMVar
-/
def isBadMatch (e : Expr) : Bool :=
  e.getAppFn.isMVar ||
  -- This extra check excludes lemmas that match a general equality
  -- these are almost never useful, and there are very many of them.
  -- We could consider removing this check.
  e.eq?.any fun (α, l, r) =>
    α.getAppFn.isMVar && l.getAppFn.isMVar && r.getAppFn.isMVar && l != r

/-- A choice of which discrimination trees to build. -/
public structure Choice where
  /-- Build the `rw` discrimination tree? -/
  rw : Bool
  /-- Build the `grw` discrimination tree? -/
  grw : Bool
  /-- Build the `apply` discrimination tree? -/
  app : Bool
  /-- Build the `apply at` discrimination tree? -/
  appAt : Bool

/--
Definition of `Choice.any` / `Choice.any` 的定义

English:
definition Choice.any
  signature: (c : Choice)
  body: c.rw || c.grw || c.app || c.appAt

中文:
定义 Choice.any
  签名: (c : Choice)
  定义体: c.rw || c.grw || c.app || c.appAt

Depends on / 依赖: c.app, c.appAt, c.grw, c.rw
-/
def Choice.any (c : Choice) : Bool := c.rw || c.grw || c.app || c.appAt

/--
Definition of `blacklist` / `blacklist` 的定义

English:
definition blacklist
  signature: (env : Environment) (declName : Name)
  body: LazyDiscrTree.blacklistInsertion env declName ||
  declName.isMetaprogramming ||
  Linter.isDeprecated env declName ||
  match declName with | .str _ s => s == "eq_def" | _ => false

中文:
定义 blacklist
  签名: (env : Environment) (declName : Name)
  定义体: LazyDiscrTree.blacklistInsertion env declName ||
  declName.isMetaprogramming ||
  Linter.isDeprecated env declName ||
  match declName with | .str _ s => s == "eq_def" | _ => false

Depends on / 依赖: LazyDiscrTree, LazyDiscrTree.blacklistInsertion, Linter, Linter.isDeprecated, blacklistInsertion, declName, declName.isMetaprogramming, eq_def, isDeprecated, isMetaprogramming
-/
def blacklist (env : Environment) (declName : Name) : Bool :=
  LazyDiscrTree.blacklistInsertion env declName ||
  declName.isMetaprogramming ||
  Linter.isDeprecated env declName ||
  match declName with | .str _ s => s == "eq_def" | _ => false

/--
Definition of `Entries.addConst` / `Entries.addConst` 的定义

English:
definition Entries.addConst
  signature: (choice : Choice) (env : Environment) (entries : Entries)
  body: do
  if cinfo.isUnsafe then return entries
  if blacklist env name then return entries
  setMCtx {}
  let (xs, _, e) ← forallMetaTelescope cinfo.type
  let mut { rw, grw, app, appAt } := entries
  -- apply
  if choice.app then
    if !isBadMatch e then
      app ← pushEntry app e ⟨.const name⟩
  -- 

中文:
定义 Entries.addConst
  签名: (choice : Choice) (env : Environment) (entries : Entries)
  定义体: do
  if cinfo.isUnsafe then return entries
  if blacklist env name then return entries
  setMCtx {}
  let (xs, _, e) ← forallMetaTelescope cinfo.type
  let mut { rw, grw, app, appAt } := entries
  -- apply
  if choice.app then
    if !isBadMatch e then
      app ← pushEntry app e ⟨.const name⟩
  -- 
-/
def Entries.addConst (choice : Choice) (env : Environment) (entries : Entries)
    (name : Name) (cinfo : ConstantInfo) : MetaM Entries := do
  if cinfo.isUnsafe then return entries
  if blacklist env name then return entries
  setMCtx {}
  let (xs, _, e) ← forallMetaTelescope cinfo.type
  let mut { rw, grw, app, appAt } := entries
  -- apply
  if choice.app then
    if !isBadMatch e then
      app ← pushEntry app e ⟨.const name⟩
  -- apply at
  if choice.appAt then
    if let some x := xs.back? then
      let e ← inferType x
      if !isBadMatch e then
        appAt ← pushEntry appAt e ⟨.const name⟩
  if choice.rw || choice.grw then
    let mkApp2 rel lhs rhs := e | pure ()
    let .const relName _ := rel.getAppFn | pure ()
    -- rw
    if relName matches ``Iff | ``Eq then
      if choice.rw then
        if !isBadMatch lhs then
          rw ← pushEntry rw lhs ⟨.const name, false⟩
        if !isBadMatch rhs && (isBadMatch lhs || !isMVarSwap lhs rhs) then
          rw ← pushEntry rw rhs ⟨.const name, true⟩
    -- grw
    else
      if choice.grw then
        if !isBadMatch lhs then
          grw ← pushEntry grw lhs ⟨.const name, false, relName⟩
        if !isBadMatch rhs then
          grw ← pushEntry grw rhs ⟨.const name, true, relName⟩
  return { rw, grw, app, appAt }

/--
Definition of `Entries.addFVar` / `Entries.addFVar` 的定义

English:
definition Entries.addFVar
  signature: (choice : Choice) (entries : Entries) (decl : LocalDecl)
  body: do
  let (xs, _, e) ← forallMetaTelescopeReducing (← instantiateMVars decl.type)
  let mut { rw, grw, app, appAt } := entries
  -- apply
  if choice.app then
    app ← pushEntry app e ⟨.fvar decl.fvarId⟩
  -- apply at
  if choice.appAt then
    if let some x := xs.back? then
      let e ← inferType 

中文:
定义 Entries.addFVar
  签名: (choice : Choice) (entries : Entries) (decl : LocalDecl)
  定义体: do
  let (xs, _, e) ← forallMetaTelescopeReducing (← instantiateMVars decl.type)
  let mut { rw, grw, app, appAt } := entries
  -- apply
  if choice.app then
    app ← pushEntry app e ⟨.fvar decl.fvarId⟩
  -- apply at
  if choice.appAt then
    if let some x := xs.back? then
      let e ← inferType 
-/
def Entries.addFVar (choice : Choice) (entries : Entries) (decl : LocalDecl) : MetaM Entries := do
  let (xs, _, e) ← forallMetaTelescopeReducing (← instantiateMVars decl.type)
  let mut { rw, grw, app, appAt } := entries
  -- apply
  if choice.app then
    app ← pushEntry app e ⟨.fvar decl.fvarId⟩
  -- apply at
  if choice.appAt then
    if let some x := xs.back? then
      let e ← inferType x
      appAt ← pushEntry appAt e ⟨.fvar decl.fvarId⟩
  -- rw
  if choice.rw then
    if let mkApp2 rel lhs rhs ← whnf e then
      if rel.getAppFn matches .const ``Iff _ | .const ``Eq _ then
        rw ← pushEntry rw lhs ⟨.fvar decl.fvarId, false⟩
        if !isMVarSwap lhs rhs then
          rw ← pushEntry rw rhs ⟨.fvar decl.fvarId, true⟩
  -- grw
  if choice.grw then
    if let mkApp2 rel lhs rhs := e.cleanupAnnotations then
      if let .const relName _ := rel.getAppFn then
        grw ← pushEntry grw lhs ⟨.fvar decl.fvarId, false, relName⟩
        grw ← pushEntry grw rhs ⟨.fvar decl.fvarId, true, relName⟩
  return { rw, grw, app, appAt }

/-- Structure used for constructing the root nodes of the 4 discrimination trees. -/
public structure PreDiscrTrees where
  /-- The `rw` discrimination tree root. -/
  rw : PreDiscrTree RwLemma := {}
  /-- The `grw` discrimination tree root. -/
  grw : PreDiscrTree GrwLemma := {}
  /-- The `apply` discrimination tree root. -/
  app : PreDiscrTree ApplyLemma := {}
  /-- The `apply at` discrimination tree root. -/
  appAt : PreDiscrTree ApplyAtLemma := {}

/--
Definition of `PreDiscrTrees.append` / `PreDiscrTrees.append` 的定义

English:
definition PreDiscrTrees.append
  signature: (pres : PreDiscrTrees) (maps : Entries)
  body: maps.rw.foldl (init := pres.rw) fun pre (key, e) => pre.push key e
  grw := maps.grw.foldl (init := pres.grw) fun pre (key, e) => pre.push key e
  app := maps.app.foldl (init := pres.app) fun pre (key, e) => pre.push key e
  appAt := maps.appAt.foldl (init := pres.appAt) fun pre (key, e) => pre.push

中文:
定义 PreDiscrTrees.append
  签名: (pres : PreDiscrTrees) (maps : Entries)
  定义体: maps.rw.foldl (init := pres.rw) fun pre (key, e) => pre.push key e
  grw := maps.grw.foldl (init := pres.grw) fun pre (key, e) => pre.push key e
  app := maps.app.foldl (init := pres.app) fun pre (key, e) => pre.push key e
  appAt := maps.appAt.foldl (init := pres.appAt) fun pre (key, e) => pre.push

Depends on / 依赖: maps.rw.foldl, pre.push, pres.rw
-/
def PreDiscrTrees.append (pres : PreDiscrTrees) (maps : Entries) : PreDiscrTrees where
  rw := maps.rw.foldl (init := pres.rw) fun pre (key, e) => pre.push key e
  grw := maps.grw.foldl (init := pres.grw) fun pre (key, e) => pre.push key e
  app := maps.app.foldl (init := pres.app) fun pre (key, e) => pre.push key e
  appAt := maps.appAt.foldl (init := pres.appAt) fun pre (key, e) => pre.push key e

/--
Definition of `librarySearchIndexConfig` / `librarySearchIndexConfig` 的定义

English:
definition librarySearchIndexConfig
  signature: : Config where
  body: .reducible
  proj := .no

中文:
定义 librarySearchIndexConfig
  签名: : Config where
  定义体: .reducible
  proj := .no

Depends on / 依赖: reducible
-/
def librarySearchIndexConfig : Config where
  transparency := .reducible
  proj := .no

/-- The global ref for looking up `rw` lemmas. -/
public initialize rwRef : IO.Ref (Option (RefinedDiscrTree RwLemma)) ← IO.mkRef none

/-- The global ref for looking up `grw` lemmas. -/
public initialize grwRef : IO.Ref (Option (RefinedDiscrTree GrwLemma)) ← IO.mkRef none

/-- The global ref for looking up `apply` lemmas. -/
public initialize appRef : IO.Ref (Option (RefinedDiscrTree ApplyLemma)) ← IO.mkRef none

/-- The global ref for looking up `apply at` lemmas. -/
public initialize appAtRef : IO.Ref (Option (RefinedDiscrTree ApplyAtLemma)) ← IO.mkRef none

/-- Compute the discrimination trees for import theorems. -/
public def computeImportDiscrTrees (choice : Choice) : CoreM Unit := do
  let choice := {
    rw := choice.rw && (← rwRef.get).isNone
    grw := choice.grw && (← grwRef.get).isNone
    app := choice.app && (← appRef.get).isNone
    appAt := choice.appAt && (← appAtRef.get).isNone
  }
  unless choice.any do return
  let (tasks, errors) ←
    foldImportedDecls {} librarySearchIndexConfig (Entries.addConst choice (← getEnv))
let pre : PreDiscrTrees ← MonadExcept.ofExcept
    tasks.foldlM (fun pre task => pre.append <$> task.get) {}
  if choice.rw then setIfNone rwRef pre.rw.toRefinedDiscrTree
  if choice.grw then setIfNone grwRef pre.grw.toRefinedDiscrTree
  if choice.app then setIfNone appRef pre.app.toRefinedDiscrTree
  if choice.appAt then setIfNone appAtRef pre.appAt.toRefinedDiscrTree
  (← errors.get).forM logError
where
  setIfNone {α} (ref : IO.Ref (Option α)) (a : α) : BaseIO Unit := do
    if (← ref.get).isNone then
      ref.set a

/-- Compute the discrimination trees for the theorems in the current file. -/
public def computeModuleDiscrTrees (choice : Choice) (parentDecl? : Option Name) :
    CoreM PreDiscrTrees := do
  let env ← getEnv
  let (pre, errors) ← foldCurrFileDecls {} librarySearchIndexConfig fun entries name cinfo => do
    if name == parentDecl? then return entries
    entries.addConst choice env name cinfo
  (← errors.get).forM logError
  return .append {} pre

/-- Compute the discrimination trees for the local variables in `lctx`.
We restrict to the variables in `lctx` to avoid using introduced bound variables. -/
public def computeLCtxDiscrTrees (choice : Choice) (lctx : LocalContext) (fvarId? : Option FVarId) :
    MetaM PreDiscrTrees := do
  let mut entries : Entries := {}
  for decl in lctx do
    if !decl.isImplementationDetail && fvarId?.all (· != decl.fvarId) then
      entries ← entries.addFVar choice decl
  return .append {} entries

/-- Get the discrimination tree matches with theorems from imported files. -/
public def getImportMatches {α} (ref : IO.Ref (Option (RefinedDiscrTree α)))
    (e : Expr) : MetaM (MatchResult α) := do
  let some tree ← ref.get |
    throwError "Internal click_suggestions error: discrimination tree was not computed."
  let (result, newTree) ← withConfig (fun _ => librarySearchIndexConfig) do
    getMatch tree e false false
  Core.checkInterrupted
  ref.set newTree
  return result

/-- Get the discrimination tree matches from `tree`. -/
public def getMatches {α} (tree : RefinedDiscrTree α) (e : Expr) : MetaM (MatchResult α) := do
  withConfig (fun _ => librarySearchIndexConfig) do
    return (← getMatch tree e false false).1

end Mathlib.Tactic.ClickSuggestions
