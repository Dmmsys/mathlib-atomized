/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init
public import Lean.Elab.Term
public import Lean.Elab.Tactic.Basic
public import Lean.Meta.Tactic.Assert
public import Lean.Meta.Tactic.Clear

/-! ## Additional utilities in `Lean.MVarId` -/

public section

open Lean Meta

namespace Lean.MVarId

/--
Definition of `«let»` / `«let»` 的定义

English:
definition «let»
  signature: (g : MVarId) (h : Name) (v : Expr) (t : Option Expr := none)
  body: do
  (← g.define h (← t.getDM (inferType v)) v).intro1P

中文:
定义 «let»
  签名: (g : MVarId) (h : Name) (v : Expr) (t : 选项类型 Expr := none)
  定义体: do
  (← g.define h (← t.getDM (inferType v)) v).intro1P
-/
def «let» (g : MVarId) (h : Name) (v : Expr) (t : Option Expr := none) :
    MetaM (FVarId × MVarId) := do
  (← g.define h (← t.getDM (inferType v)) v).intro1P

/--
Definition of `existsi` / `existsi` 的定义

English:
definition existsi
  signature: (mvar : MVarId) (es : List Expr)
  body: do
  es.foldlM (fun mv e => do
let (subgoals,_) ← Elab.Term.TermElabM.run Elab.Tactic.run mv do
        Elab.Tactic.evalTactic (← `(tactic| refine ⟨?_,?_⟩))
      let [sg1, sg2] := subgoals | throwError "expected two subgoals"
      sg1.assign e
      pure sg2)
    mvar

中文:
定义 存在i
  签名: (mvar : MVarId) (es : 列表 Expr)
  定义体: do
  es.foldlM (fun mv e => do
let (subgoals,_) ← Elab.Term.TermElabM.run Elab.Tactic.run mv do
        Elab.Tactic.evalTactic (← `(tactic| refine ⟨?_,?_⟩))
      let [sg1, sg2] := subgoals | throwError "expected two subgoals"
      sg1.assign e
      pure sg2)
    mvar
-/
def existsi (mvar : MVarId) (es : List Expr) : MetaM MVarId := do
  es.foldlM (fun mv e => do
let (subgoals,_) ← Elab.Term.TermElabM.run Elab.Tactic.run mv do
        Elab.Tactic.evalTactic (← `(tactic| refine ⟨?_,?_⟩))
      let [sg1, sg2] := subgoals | throwError "expected two subgoals"
      sg1.assign e
      pure sg2)
    mvar

/--
Definition of `intros!` / `intros!` 的定义

English:
definition intros!
  signature: (mvarId : MVarId)
  body: run #[] mvarId

中文:
定义 intros!
  签名: (mvarId : MVarId)
  定义体: run #[] mvarId
-/
partial def intros! (mvarId : MVarId) : MetaM (Array FVarId × MVarId) :=
  run #[] mvarId
where
  /-- Implementation of `intros!`. -/
  run (acc : Array FVarId) (g : MVarId) :=
    try
      let ⟨f, g⟩ ← mvarId.intro1
      run (acc.push f) g
    catch _ =>
      pure (acc, g)

end Lean.MVarId

namespace Lean.Meta

/--
Definition of `_root_.Lean.MVarId.getType''` / `_root_.Lean.MVarId.getType''` 的定义

English:
definition _root_.Lean.MVarId.getType''
  signature: (mvarId : MVarId)
  body: return (← instantiateMVars (← mvarId.getType)).cleanupAnnotations

中文:
定义 _root_.Lean.MVarId.getType''
  签名: (mvarId : MVarId)
  定义体: return (← instantiateMVars (← mvarId.getType)).cleanupAnnotations

Depends on / 依赖: cleanupAnnotations, getType, instantiateMVars, mvarId, mvarId.getType, return
-/
def _root_.Lean.MVarId.getType'' (mvarId : MVarId) : MetaM Expr :=
  return (← instantiateMVars (← mvarId.getType)).cleanupAnnotations

end Lean.Meta

namespace Lean.Elab.Tactic

-- I'd prefer to call that `liftMetaTactic1`,
-- but that is taken in core by a function that lifts a `tac : MVarId → MetaM (Option MVarId)`.
/--
Definition of `liftMetaTactic'` / `liftMetaTactic'` 的定义

English:
definition liftMetaTactic'
  signature: (tac : MVarId -> MetaM MVarId)
  body: liftMetaTactic fun g => do pure [← tac g]

中文:
定义 liftMetaTactic'
  签名: (tac : MVarId -> MetaM MVarId)
  定义体: liftMetaTactic fun g => do pure [← tac g]

Depends on / 依赖: liftMetaTactic
-/
def liftMetaTactic' (tac : MVarId -> MetaM MVarId) : TacticM Unit :=
  liftMetaTactic fun g => do pure [← tac g]

variable {α : Type}

/--
Definition of `TacticM.runCore` / `TacticM.runCore` 的定义

English:
definition TacticM.runCore
  signature: (x : TacticM α) (ctx : Context) (s : State)
  body: .run s x ctx

中文:
定义 TacticM.runCore
  签名: (x : TacticM α) (ctx : 余ntext) (s : State)
  定义体: .run s x ctx
-/
@[inline] private def TacticM.runCore (x : TacticM α) (ctx : Context) (s : State) :
    TermElabM (α × State) :=
.run s x ctx

/--
Definition of `TacticM.runCore'` / `TacticM.runCore'` 的定义

English:
definition TacticM.runCore'
  signature: (x : TacticM α) (ctx : Context) (s : State)
  body: Prod.fst < > x.runCore ctx s

中文:
定义 TacticM.runCore'
  签名: (x : TacticM α) (ctx : 余ntext) (s : State)
  定义体: Prod.fst < > x.runCore ctx s
-/
@[inline] private def TacticM.runCore' (x : TacticM α) (ctx : Context) (s : State) : TermElabM α :=
Prod.fst < > x.runCore ctx s

-- We need this because Lean 4 core only provides `TacticM` functions for building simp contexts,
-- making it quite painful to call `simp` from `MetaM`.
/--
Definition of `run_for` / `run_for` 的定义

English:
definition run_for
  signature: (mvarId : MVarId) (x : TacticM α)
  body: mvarId.withContext do
    let pendingMVarsSaved := (← get).pendingMVars
    modify fun s => { s with pendingMVars := [] }
    let aux : TacticM (Option α × List MVarId) :=
      /- Important: the following `try` does not backtrack the state.
          This is intentional because we don't want to backtrack the error message
          when we catch the "abort internal exception"
          We must define `run` here because we define `MonadExcept` instance for `TacticM` -/
      try
        let a ← x
        pure (a, ← getUnsolvedGoals)
      catch ex =>
        if isAbortTacticException ex then
          pure (none, ← getUnsolvedGoals)
        else
          throw ex
    try
      aux.runCore' { elaborator := .anonymous } { goals := [mvarId] }
    finally
      modify fun s => { s with pendingMVars := pendingMVarsSaved }

中文:
定义 run_for
  签名: (mvarId : MVarId) (x : TacticM α)
  定义体: mvarId.withContext do
    let pendingMVarsSaved := (← get).pendingMVars
    modify fun s => { s with pendingMVars := [] }
    let aux : TacticM (Option α × List MVarId) :=
      /- Important: the following `try` does not backtrack the state.
          This is intentional because we don't want to backtrack the error message
          when we catch the "abort internal exception"
          We must define `run` here because we define `MonadExcept` instance for `TacticM` -/
      try
        let a ← x
        pure (a, ← getUnsolvedGoals)
      catch ex =>
        if isAbortTacticException ex then
          pure (none, ← getUnsolvedGoals)
        else
          throw ex
    try
      aux.runCore' { elaborator := .anonymous } { goals := [mvarId] }
    finally
      modify fun s => { s with pendingMVars := pendingMVarsSaved }

Depends on / 依赖: MVarId, TacticM, modify, mvarId, mvarId.withContext, pendingMVars, pendingMVarsSaved, withContext
-/
def run_for (mvarId : MVarId) (x : TacticM α) : TermElabM (Option α × List MVarId) :=
  mvarId.withContext do
    let pendingMVarsSaved := (← get).pendingMVars
    modify fun s => { s with pendingMVars := [] }
    let aux : TacticM (Option α × List MVarId) :=
      /- Important: the following `try` does not backtrack the state.
          This is intentional because we don't want to backtrack the error message
          when we catch the "abort internal exception"
          We must define `run` here because we define `MonadExcept` instance for `TacticM` -/
      try
        let a ← x
        pure (a, ← getUnsolvedGoals)
      catch ex =>
        if isAbortTacticException ex then
          pure (none, ← getUnsolvedGoals)
        else
          throw ex
    try
      aux.runCore' { elaborator := .anonymous } { goals := [mvarId] }
    finally
      modify fun s => { s with pendingMVars := pendingMVarsSaved }

end Lean.Elab.Tactic
