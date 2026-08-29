/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public meta import Mathlib.Lean.Elab.Tactic.Meta
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header -- shake: keep

/-! # Executing actions using the infotree

This file contains helper functions for running `CoreM`, `MetaM` and tactic actions
in the context of an infotree node.
-/

@[expose] public meta section

open Lean Elab Term Command Linter

namespace Lean.Elab.ContextInfo

variable {α}

/--
Definition of `runCoreMWithMessages` / `runCoreMWithMessages` 的定义

English:
definition runCoreMWithMessages
  signature: (info : ContextInfo) (x : CoreM α)
  body: do
  -- We assume that this function is used only outside elaboration, mostly in the language server,
  -- and so we can and should provide access to information regardless whether it is exported.
  let env := info.env.setExporting false
  let ctx ← read
  /-
    We must execute `x` using the `ngen`

中文:
定义 runCoreMWithMessages
  签名: (info : ContextInfo) (x : CoreM α)
  定义体: do
  -- We assume that this function is used only outside elaboration, mostly in the language server,
  -- and so we can and should provide access to information regardless whether it is exported.
  let env := info.env.setExporting false
  let ctx ← read
  /-
    We must execute `x` using the `ngen`
-/
def runCoreMWithMessages (info : ContextInfo) (x : CoreM α) : CommandElabM α := do
  -- We assume that this function is used only outside elaboration, mostly in the language server,
  -- and so we can and should provide access to information regardless whether it is exported.
  let env := info.env.setExporting false
  let ctx ← read
  /-
    We must execute `x` using the `ngen` stored in `info`. Otherwise, we may create `MVarId`s and
    `FVarId`s that have been used in `lctx` and `info.mctx`.
    Similarly, we need to pass in a `namePrefix` because otherwise we can't create auxiliary
    definitions.
  -/
  let (x, newState) ←
    (withOptions (fun _ => info.options) x).toIO
      { currNamespace := info.currNamespace, openDecls := info.openDecls
        fileName := ctx.fileName, fileMap := ctx.fileMap }
      { env, ngen := info.ngen, auxDeclNGen := { namePrefix := info.parentDecl?.getD .anonymous } }
  -- Migrate logs back to the main context.
  modify fun state => { state with
    messages := state.messages ++ newState.messages,
    traceState.traces := state.traceState.traces ++ newState.traceState.traces }
  return x

/--
Definition of `runMetaMWithMessages` / `runMetaMWithMessages` 的定义

English:
definition runMetaMWithMessages
  signature: (info : ContextInfo) (lctx : LocalContext) (x : MetaM α)
  body: do
(·.1) < > info.runCoreMWithMessages (Lean.Meta.MetaM.run
(ctx := { lctx := lctx }) (s := { mctx := info.mctx })
    -- Update the local instances, otherwise typeclass search would fail to see anything in the
    -- local context.
Meta.withLocalInstances (lctx.decls.toList.filterMap id) x)

中文:
定义 runMetaMWithMessages
  签名: (info : ContextInfo) (lctx : LocalContext) (x : MetaM α)
  定义体: do
(·.1) < > info.runCoreMWithMessages (Lean.Meta.MetaM.run
(ctx := { lctx := lctx }) (s := { mctx := info.mctx })
    -- Update the local instances, otherwise typeclass search would fail to see anything in the
    -- local context.
Meta.withLocalInstances (lctx.decls.toList.filterMap id) x)
-/
def runMetaMWithMessages (info : ContextInfo) (lctx : LocalContext) (x : MetaM α) : CommandElabM α := do
(·.1) < > info.runCoreMWithMessages (Lean.Meta.MetaM.run
(ctx := { lctx := lctx }) (s := { mctx := info.mctx })
    -- Update the local instances, otherwise typeclass search would fail to see anything in the
    -- local context.
Meta.withLocalInstances (lctx.decls.toList.filterMap id) x)

/--
Definition of `runTactic` / `runTactic` 的定义

English:
definition runTactic
  signature: (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId) (x : MVarId -> MetaM α)
  body: do
  if !i.goalsBefore.contains goal then
    panic!"ContextInfo.runTactic: `goal` must be an element of `i.goalsBefore`"
  let mctx := i.mctxBefore
  let lctx := (mctx.decls.find! goal).2
  ctx.runMetaMWithMessages lctx do
    -- Make a fresh metavariable because the original goal is already assign

中文:
定义 runTactic
  签名: (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId) (x : MVarId -> MetaM α)
  定义体: do
  if !i.goalsBefore.contains goal then
    panic!"ContextInfo.runTactic: `goal` must be an element of `i.goalsBefore`"
  let mctx := i.mctxBefore
  let lctx := (mctx.decls.find! goal).2
  ctx.runMetaMWithMessages lctx do
    -- Make a fresh metavariable because the original goal is already assign
-/
def runTactic (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId) (x : MVarId -> MetaM α) :
    CommandElabM α := do
  if !i.goalsBefore.contains goal then
    panic!"ContextInfo.runTactic: `goal` must be an element of `i.goalsBefore`"
  let mctx := i.mctxBefore
  let lctx := (mctx.decls.find! goal).2
  ctx.runMetaMWithMessages lctx do
    -- Make a fresh metavariable because the original goal is already assigned.
    let type ← goal.getType
    let goal ← Meta.mkFreshExprSyntheticOpaqueMVar type
    x goal.mvarId!

/--
Definition of `runTacticCode` / `runTacticCode` 的定义

English:
definition runTacticCode
  signature: (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId) (code : Syntax)
  body: do
  let termCtx ← liftTermElabM read
  let termState ← liftTermElabM get
  ctx.runTactic i goal fun goal => do
    let newGoals ← Lean.Elab.runTactic' (ctx := termCtx) (s := termState) goal code
    newGoals.mapM m.2

中文:
定义 runTacticCode
  签名: (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId) (code : Syntax)
  定义体: do
  let termCtx ← liftTermElabM read
  let termState ← liftTermElabM get
  ctx.runTactic i goal fun goal => do
    let newGoals ← Lean.Elab.runTactic' (ctx := termCtx) (s := termState) goal code
    newGoals.mapM m.2

Depends on / 依赖: MVarId
-/
def runTacticCode (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId) (code : Syntax)
    (m : Σ α : Type, MVarId -> MetaM α := ⟨MVarId, pure⟩) :
    CommandElabM (List m.1) := do
  let termCtx ← liftTermElabM read
  let termState ← liftTermElabM get
  ctx.runTactic i goal fun goal => do
    let newGoals ← Lean.Elab.runTactic' (ctx := termCtx) (s := termState) goal code
    newGoals.mapM m.2

/--
Definition of `runCoreMCapturingInfoTree` / `runCoreMCapturingInfoTree` 的定义

English:
definition runCoreMCapturingInfoTree
  signature: (info : ContextInfo) (x : CoreM α)
  body: do
  let env := info.env.setExporting false
  let ctx ← read
  let (result, newState) ←
    (withOptions (fun _ => info.options) x).toIO
      { currNamespace := info.currNamespace, openDecls := info.openDecls
        fileName := ctx.fileName, fileMap := ctx.fileMap }
      { env, ngen := info.ngen,

中文:
定义 runCoreMCapturingInfoTree
  签名: (info : ContextInfo) (x : CoreM α)
  定义体: do
  let env := info.env.setExporting false
  let ctx ← read
  let (result, newState) ←
    (withOptions (fun _ => info.options) x).toIO
      { currNamespace := info.currNamespace, openDecls := info.openDecls
        fileName := ctx.fileName, fileMap := ctx.fileMap }
      { env, ngen := info.ngen,
-/
def runCoreMCapturingInfoTree (info : ContextInfo) (x : CoreM α) :
    CommandElabM (α × PersistentArray InfoTree) := do
  let env := info.env.setExporting false
  let ctx ← read
  let (result, newState) ←
    (withOptions (fun _ => info.options) x).toIO
      { currNamespace := info.currNamespace, openDecls := info.openDecls
        fileName := ctx.fileName, fileMap := ctx.fileMap }
      { env, ngen := info.ngen, auxDeclNGen := { namePrefix := info.parentDecl?.getD .anonymous } }
  -- Migrate logs back to the main context
  modify fun state => { state with
    messages := state.messages ++ newState.messages,
    traceState.traces := state.traceState.traces ++ newState.traceState.traces }
  return (result, newState.infoState.trees)

/--
Definition of `runMetaMCapturingInfoTree` / `runMetaMCapturingInfoTree` 的定义

English:
definition runMetaMCapturingInfoTree
  signature: (info : ContextInfo) (lctx : LocalContext) (x : MetaM α)
  body: do
  let (result, trees) ← info.runCoreMCapturingInfoTree (Lean.Meta.MetaM.run
(ctx := { lctx := lctx }) (s := { mctx := info.mctx })
Meta.withLocalInstances (lctx.decls.toList.filterMap id) x)
  return (result.1, trees)

中文:
定义 runMetaMCapturingInfoTree
  签名: (info : ContextInfo) (lctx : LocalContext) (x : MetaM α)
  定义体: do
  let (result, trees) ← info.runCoreMCapturingInfoTree (Lean.Meta.MetaM.run
(ctx := { lctx := lctx }) (s := { mctx := info.mctx })
Meta.withLocalInstances (lctx.decls.toList.filterMap id) x)
  return (result.1, trees)
-/
def runMetaMCapturingInfoTree (info : ContextInfo) (lctx : LocalContext) (x : MetaM α) :
    CommandElabM (α × PersistentArray InfoTree) := do
  let (result, trees) ← info.runCoreMCapturingInfoTree (Lean.Meta.MetaM.run
(ctx := { lctx := lctx }) (s := { mctx := info.mctx })
Meta.withLocalInstances (lctx.decls.toList.filterMap id) x)
  return (result.1, trees)

/--
Definition of `runTacticCapturingInfoTree` / `runTacticCapturingInfoTree` 的定义

English:
definition runTacticCapturingInfoTree
  signature: (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId)
  body: do
  if !i.goalsBefore.contains goal then
    panic!"ContextInfo.runTacticCapturingInfoTree: `goal` must be an element of `i.goalsBefore`"
  let mctx := i.mctxBefore
  let lctx := (mctx.decls.find! goal).2
  ctx.runMetaMCapturingInfoTree lctx do
    let type ← goal.getType
    let goal ← Meta.mkFres

中文:
定义 runTacticCapturingInfoTree
  签名: (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId)
  定义体: do
  if !i.goalsBefore.contains goal then
    panic!"ContextInfo.runTacticCapturingInfoTree: `goal` must be an element of `i.goalsBefore`"
  let mctx := i.mctxBefore
  let lctx := (mctx.decls.find! goal).2
  ctx.runMetaMCapturingInfoTree lctx do
    let type ← goal.getType
    let goal ← Meta.mkFres
-/
def runTacticCapturingInfoTree (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId)
    (x : MVarId -> MetaM α) : CommandElabM (α × PersistentArray InfoTree) := do
  if !i.goalsBefore.contains goal then
    panic!"ContextInfo.runTacticCapturingInfoTree: `goal` must be an element of `i.goalsBefore`"
  let mctx := i.mctxBefore
  let lctx := (mctx.decls.find! goal).2
  ctx.runMetaMCapturingInfoTree lctx do
    let type ← goal.getType
    let goal ← Meta.mkFreshExprSyntheticOpaqueMVar type
    x goal.mvarId!

/--
Definition of `runTacticCodeCapturingInfoTree` / `runTacticCodeCapturingInfoTree` 的定义

English:
definition runTacticCodeCapturingInfoTree
  signature: (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId)
  body: do
  let termCtx ← liftTermElabM read
  let termState ← liftTermElabM get
  ctx.runTacticCapturingInfoTree i goal fun goal => do
    Lean.Elab.runTactic' (ctx := termCtx) (s := termState) goal code

中文:
定义 runTacticCodeCapturingInfoTree
  签名: (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId)
  定义体: do
  let termCtx ← liftTermElabM read
  let termState ← liftTermElabM get
  ctx.runTacticCapturingInfoTree i goal fun goal => do
    Lean.Elab.runTactic' (ctx := termCtx) (s := termState) goal code
-/
def runTacticCodeCapturingInfoTree (ctx : ContextInfo) (i : TacticInfo) (goal : MVarId)
    (code : Syntax) : CommandElabM (List MVarId × PersistentArray InfoTree) := do
  let termCtx ← liftTermElabM read
  let termState ← liftTermElabM get
  ctx.runTacticCapturingInfoTree i goal fun goal => do
    Lean.Elab.runTactic' (ctx := termCtx) (s := termState) goal code

end Lean.Elab.ContextInfo
