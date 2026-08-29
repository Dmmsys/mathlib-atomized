/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.Location
public meta import Lean.Meta.Tactic.Simp.Main
public import Lean.Elab.Tactic.Location

/-!
# Rewriting at specified locations

Many metaprograms have the following general structure: the input is an expression `e` and the
output is a new expression `e'`, together with a proof that `e = e'`.

This file provides convenience functions to turn such a metaprogram into a variety of tactics:
using the metaprogram to modify the goal, a specified hypothesis, or (via `Tactic.Location`) a
combination of these.
-/

public meta section

/--
Definition of `Lean.Elab.Tactic.withNondepPropLocation` / `Lean.Elab.Tactic.withNondepPropLocation` 的定义

English:
definition Lean.Elab.Tactic.withNondepPropLocation
  signature: (loc : Location) (atLocal : FVarId -> TacticM Unit)
  body: do
  match loc with
  | Location.targets hyps target => do
    (← getFVarIds hyps).forM atLocal
    if target then atTarget
  | Location.wildcard => do
    let mut worked := false
    for hyp in ← (← getMainGoal).getNondepPropHyps do
      worked := worked || (← tryTactic <| atLocal hyp)
    unless 

中文:
定义 Lean.Elab.Tactic.withNondepPropLocation
  签名: (loc : Location) (atLocal : FVarId -> TacticM 单元)
  定义体: do
  match loc with
  | Location.targets hyps target => do
    (← getFVarIds hyps).forM atLocal
    if target then atTarget
  | Location.wildcard => do
    let mut worked := false
    for hyp in ← (← getMainGoal).getNondepPropHyps do
      worked := worked || (← tryTactic <| atLocal hyp)
    unless 
-/
def Lean.Elab.Tactic.withNondepPropLocation (loc : Location) (atLocal : FVarId -> TacticM Unit)
    (atTarget : TacticM Unit) (failed : MVarId -> TacticM Unit) : TacticM Unit := do
  match loc with
  | Location.targets hyps target => do
    (← getFVarIds hyps).forM atLocal
    if target then atTarget
  | Location.wildcard => do
    let mut worked := false
    for hyp in ← (← getMainGoal).getNondepPropHyps do
      worked := worked || (← tryTactic <| atLocal hyp)
    unless worked || (← tryTactic atTarget) do
      failed (← getMainGoal)

namespace Mathlib.Tactic
open Lean Meta Elab.Tactic

/--
Inductive type `BehaviorIfUnchanged` / 归纳类型 `BehaviorIfUnchanged`

English:
inductive BehaviorIfUnchanged
  parameters: where
  constructors (3):
    - silent: 
    - warning: 
    - error: 

中文:
归纳类型 BehaviorIfUnchanged
  参数: where
  构造子 (3 个):
    - silent: 
    - warning: 
    - error: 
-/
inductive BehaviorIfUnchanged where
  /-- Stay silent if this action has no effect. -/
  | silent
  /-- Log a warning if this action has no effect. -/
  | warning
  /-- Throw an error if this action has no effect. -/
  | error
deriving BEq, Inhabited, Repr

/--
Definition of `transformAtTarget` / `transformAtTarget` 的定义

English:
definition transformAtTarget
  signature: (m : Expr -> ReaderT Simp.Context MetaM Simp.Result) (proc : String)
  body: do
  let tgt ← instantiateMVars (← goal.getType)
  let r ← m tgt
  -- we use expression equality here (rather than defeq) to be consistent with, e.g.,
  -- `applySimpResultToTarget`
  let unchanged := tgt.cleanupAnnotations == r.expr.cleanupAnnotations
  if unchanged then
    match ifUnchanged with


中文:
定义 transformAtTarget
  签名: (m : Expr -> ReaderT Simp.余ntext MetaM Simp.Result) (proc : String)
  定义体: do
  let tgt ← instantiateMVars (← goal.getType)
  let r ← m tgt
  -- we use expression equality here (rather than defeq) to be consistent with, e.g.,
  -- `applySimpResultToTarget`
  let unchanged := tgt.cleanupAnnotations == r.expr.cleanupAnnotations
  if unchanged then
    match ifUnchanged with

-/
def transformAtTarget (m : Expr -> ReaderT Simp.Context MetaM Simp.Result) (proc : String)
    (ifUnchanged : BehaviorIfUnchanged) (goal : MVarId) :
    ReaderT Simp.Context MetaM (Option MVarId) := do
  let tgt ← instantiateMVars (← goal.getType)
  let r ← m tgt
  -- we use expression equality here (rather than defeq) to be consistent with, e.g.,
  -- `applySimpResultToTarget`
  let unchanged := tgt.cleanupAnnotations == r.expr.cleanupAnnotations
  if unchanged then
    match ifUnchanged with
    | .warning => logWarning m!"`{proc}` made no progress on the goal"
    | .error => throwError "`{proc}` made no progress on the goal"
    | .silent => pure ()
  if r.expr.isTrue then
    goal.assign (← mkOfEqTrue (← r.getProof))
    pure none
  else
    -- this ensures that we really get the same goal as an `MVarId`,
    -- not a different `MVarId` for which `MVarId.getType` is the same
    if unchanged then return goal
    applySimpResultToTarget goal tgt r

/--
Definition of `transformAtLocalDecl` / `transformAtLocalDecl` 的定义

English:
definition transformAtLocalDecl
  signature: (m : Expr -> ReaderT Simp.Context MetaM Simp.Result) (proc : String)
  body: do
  let ldecl ← fvarId.getDecl
  if ldecl.isImplementationDetail then
    throwError "Cannot run `{proc}` at `{Expr.fvar fvarId}`, it is an implementation detail"
  let tgt ← instantiateMVars (← fvarId.getType)
  let eraseFVarId (ctx : Simp.Context) :=
ctx.setSimpTheorems ctx.simpTheorems.eraseTheo

中文:
定义 transformAtLocalDecl
  签名: (m : Expr -> ReaderT Simp.余ntext MetaM Simp.Result) (proc : String)
  定义体: do
  let ldecl ← fvarId.getDecl
  if ldecl.isImplementationDetail then
    throwError "Cannot run `{proc}` at `{Expr.fvar fvarId}`, it is an implementation detail"
  let tgt ← instantiateMVars (← fvarId.getType)
  let eraseFVarId (ctx : Simp.Context) :=
ctx.setSimpTheorems ctx.simpTheorems.eraseTheo
-/
def transformAtLocalDecl (m : Expr -> ReaderT Simp.Context MetaM Simp.Result) (proc : String)
    (ifUnchanged : BehaviorIfUnchanged) (mayCloseGoal : Bool) (fvarId : FVarId) (goal : MVarId) :
    ReaderT Simp.Context MetaM (Option MVarId) := do
  let ldecl ← fvarId.getDecl
  if ldecl.isImplementationDetail then
    throwError "Cannot run `{proc}` at `{Expr.fvar fvarId}`, it is an implementation detail"
  let tgt ← instantiateMVars (← fvarId.getType)
  let eraseFVarId (ctx : Simp.Context) :=
ctx.setSimpTheorems ctx.simpTheorems.eraseTheorem (.fvar fvarId)
let r ← withReader eraseFVarId m tgt
  -- we use expression equality here (rather than defeq) to be consistent with, e.g.,
  -- `applySimpResultToLocalDeclCore`
  if tgt.cleanupAnnotations == r.expr.cleanupAnnotations then
    match ifUnchanged with
    | .warning => logWarning m!"`{proc}` made no progress at `{Expr.fvar fvarId}`"
    | .error => throwError "`{proc}` made no progress at `{Expr.fvar fvarId}`"
    | .silent => pure ()
  return (← applySimpResultToLocalDecl goal fvarId r mayCloseGoal).map Prod.snd

/--
Definition of `transformAtLocation` / `transformAtLocation` 的定义

English:
definition transformAtLocation
  signature: (m : Expr -> ReaderT Simp.Context MetaM Simp.Result) (proc : String)
  body: withLocation loc
    (liftMetaTactic1 ∘ (transformAtLocalDecl m proc ifUnchanged mayCloseGoalFromHyp · · ctx))
    (liftMetaTactic1 (transformAtTarget m proc ifUnchanged · ctx))
    fun _ => throwError "`{proc}` made no progress anywhere"

中文:
定义 transformAtLocation
  签名: (m : Expr -> ReaderT Simp.余ntext MetaM Simp.Result) (proc : String)
  定义体: withLocation loc
    (liftMetaTactic1 ∘ (transformAtLocalDecl m proc ifUnchanged mayCloseGoalFromHyp · · ctx))
    (liftMetaTactic1 (transformAtTarget m proc ifUnchanged · ctx))
    fun _ => throwError "`{proc}` made no progress anywhere"
-/
def transformAtLocation (m : Expr -> ReaderT Simp.Context MetaM Simp.Result) (proc : String)
    (loc : Location) (ifUnchanged : BehaviorIfUnchanged := .error)
    (mayCloseGoalFromHyp : Bool := false)
    -- streamline the most common use case, in which the procedure `m`'s implementation is not
    -- simp-based and its `Simp.Context` is ignored
    (ctx : Simp.Context := default) :
    TacticM Unit :=
  withLocation loc
    (liftMetaTactic1 ∘ (transformAtLocalDecl m proc ifUnchanged mayCloseGoalFromHyp · · ctx))
    (liftMetaTactic1 (transformAtTarget m proc ifUnchanged · ctx))
    fun _ => throwError "`{proc}` made no progress anywhere"

/--
Definition of `transformAtNondepPropLocation` / `transformAtNondepPropLocation` 的定义

English:
definition transformAtNondepPropLocation
  signature: (m : Expr -> ReaderT Simp.Context MetaM Simp.Result)
  body: withNondepPropLocation loc
    (liftMetaTactic1 ∘ (transformAtLocalDecl m proc ifUnchanged mayCloseGoalFromHyp · · ctx))
    (liftMetaTactic1 (transformAtTarget m proc ifUnchanged · ctx))
    fun _ => throwError "`{proc}` made no progress anywhere"

中文:
定义 transformAtNondepPropLocation
  签名: (m : Expr -> ReaderT Simp.余ntext MetaM Simp.Result)
  定义体: withNondepPropLocation loc
    (liftMetaTactic1 ∘ (transformAtLocalDecl m proc ifUnchanged mayCloseGoalFromHyp · · ctx))
    (liftMetaTactic1 (transformAtTarget m proc ifUnchanged · ctx))
    fun _ => throwError "`{proc}` made no progress anywhere"
-/
def transformAtNondepPropLocation (m : Expr -> ReaderT Simp.Context MetaM Simp.Result)
    (proc : String) (loc : Location) (ifUnchanged : BehaviorIfUnchanged := .error)
    (mayCloseGoalFromHyp : Bool := false)
    -- streamline the most common use case, in which the procedure `m`'s implementation is not
    -- simp-based and its `Simp.Context` is ignored
    (ctx : Simp.Context := default) :
    TacticM Unit :=
  withNondepPropLocation loc
    (liftMetaTactic1 ∘ (transformAtLocalDecl m proc ifUnchanged mayCloseGoalFromHyp · · ctx))
    (liftMetaTactic1 (transformAtTarget m proc ifUnchanged · ctx))
    fun _ => throwError "`{proc}` made no progress anywhere"

end Mathlib.Tactic
