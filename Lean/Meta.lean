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

/-- Add the hypothesis `h : t`, given `v : t`, and return the new `FVarId`. -/
/-
**Lean.MVarId.** 是 Mathlib 中的一个定义，位于命名空间 `Lean.MVarId`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Add the hypothesis `h : t`, given `v : t`, and return the new `FVarId`.
-/
def «let» (g : MVarId) (h : Name) (v : Expr) (t : Option Expr := none) :
    MetaM (FVarId × MVarId) := do
  (← g.define h (← t.getDM (inferType v)) v).intro1P

/-- Has the effect of `refine ⟨e₁,e₂,⋯, ?_⟩`.
-/
/-
**Lean.MVarId.existsi** 是 Mathlib 中的一个定义，位于命名空间 `Lean.MVarId`。
形式化陈述：existsi (mvar : MVarId) (es : List Expr) : MetaM MVarId
参数：mvar : MVarId；es : List Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Has the effect of `refine ⟨e₁,e₂,⋯, ?_⟩`.
-/
def existsi (mvar : MVarId) (es : List Expr) : MetaM MVarId := do
  es.foldlM (fun mv e ↦ do
      let (subgoals,_) ← Elab.Term.TermElabM.run <| Elab.Tactic.run mv do
        Elab.Tactic.evalTactic (← `(tactic| refine ⟨?_,?_⟩))
      let [sg1, sg2] := subgoals | throwError "expected two subgoals"
      sg1.assign e
      pure sg2)
    mvar

/-- Applies `intro` repeatedly until it fails. We use this instead of
`Lean.MVarId.intros` to allowing unfolding.
For example, if we want to do introductions for propositions like `¬p`,
the `¬` needs to be unfolded into `→ False`, and `intros` does not do such unfolding. -/
/-
**Lean.MVarId.intros** 是 Mathlib 中的一个定义，位于命名空间 `Lean.MVarId`。
形式化陈述：MVarId → MetaM (Array FVarId × MVarId)
参数：Array FVarId × MVarId。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies `intro` repeatedly until it fails. We use this instead of
`Lean.MVarId.intros` to allowing unfolding.
For example, if we want to do introductions for propositions like `¬p`,
the `¬` needs to be unfolded into `→ False`, and `intros` does not do such unfol
ding.
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

/-- Get the type the given metavariable after instantiating metavariables and cleaning up
annotations. -/
/-
**Lean.Meta._root_.Lean.MVarId.getType''** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Meta`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the type the given metavariable after instantiating metavariables and cleani
ng up
annotations.
-/
def _root_.Lean.MVarId.getType'' (mvarId : MVarId) : MetaM Expr :=
  return (← instantiateMVars (← mvarId.getType)).cleanupAnnotations

end Lean.Meta

namespace Lean.Elab.Tactic

/-- Analogue of `liftMetaTactic` for tactics that return a single goal. -/
-- I'd prefer to call that `liftMetaTactic1`,
-- but that is taken in core by a function that lifts a `tac : MVarId → MetaM (Option MVarId)`.
/-
**Lean.Elab.Tactic.liftMetaTactic'** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic`。
形式化陈述：liftMetaTactic' (tac : MVarId -> MetaM MVarId) : TacticM Unit
参数：tac : MVarId -> MetaM MVarId。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def liftMetaTactic' (tac : MVarId → MetaM MVarId) : TacticM Unit :=
  liftMetaTactic fun g => do pure [← tac g]

variable {α : Type}
/-
**Lean.Elab.Tactic.TacticM.runCore** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[inline] private def TacticM.runCore (x : TacticM α) (ctx : Context) (s : State) :
    TermElabM (α × State) :=
  x ctx |>.run s
/-
**Lean.Elab.Tactic.TacticM.runCore'** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[inline] private def TacticM.runCore' (x : TacticM α) (ctx : Context) (s : State) : TermElabM α :=
  Prod.fst <$> x.runCore ctx s

/-- Copy of `Lean.Elab.Tactic.run` that can return a value. -/
-- We need this because Lean 4 core only provides `TacticM` functions for building simp contexts,
-- making it quite painful to call `simp` from `MetaM`.
/-
**Lean.Elab.Tactic.run_for** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic`。
形式化陈述：run_for (mvarId : MVarId) (x : TacticM α) : TermElabM (Option α × List MVa
rId)
参数：mvarId : MVarId；x : TacticM α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

