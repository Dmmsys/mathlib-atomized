/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, David Renshaw
-/
module

public meta import Lean.Elab.Tactic.Classical
public meta import Lean.Elab.Tactic.Config
public import Mathlib.Logic.Basic -- shake: keep (dependency of tactic output)
public meta import Qq
public meta import Mathlib.Lean.Meta
public import Mathlib.Tactic.CasesM
public import Mathlib.Tactic.Core

/-!
The `tauto` tactic.
-/

public meta section

namespace Mathlib.Tactic.Tauto

open Lean Elab.Tactic Parser.Tactic Lean.Meta MVarId Batteries.Tactic
open Qq

initialize registerTraceClass `tauto

/--
Definition of `distribNotOnceAt` / `distribNotOnceAt` 的定义

English:
definition distribNotOnceAt
  signature: (hypFVar : Expr) (g : MVarId)
  body: g.withContext do
  let .fvar fvarId := hypFVar | throwError "not fvar {hypFVar}"
  let h ← fvarId.getDecl
  let e : Q(Prop) ← (do guard <| ← Meta.isProp h.type; pure h.type)
  let replace (p : Expr) : MetaM AssertAfterResult := do
    commitIfNoEx do
      let result ← g.assertAfter fvarId h.userName (← inferType p) p
      /-
        We attempt to clear the old hypothesis. Doing so is crucial for
        avoiding infinite loops. On failure, we roll back the MetaM state
        and ignore this hypothesis. See
        https://github.com/leanprover-community/mathlib4/issues/10590.
      -/
      let newGoal ← result.mvarId.clear fvarId
      return { result with mvarId := newGoal }

  match e with
  | ~q(¬ ($a : Prop) = $b) => do
    let h' : Q(¬$a = $b) := h.toExpr
    replace q(mt propext $h')
  | ~q(($a : Prop) = $b) => do
    let h' : Q($a = $b) := h.toExpr
    replace q(Eq.to_iff $h')
  | ~q(¬ (($a : Prop) ∧ $b)) => do
    let h' : Q(¬($a ∧ $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $b)
    replace q(Decidable.not_and_iff_not_or_not'.mp $h')
  | ~q(¬ (($a : Prop) ∨ $b)) => do
    let h' : Q(¬($a ∨ $b)) := h.toExpr
    replace q(not_or.mp $h')
  | ~q(¬ (($a : Prop) != $b)) => do
    let h' : Q(¬($a != $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable ($a = $b))
    replace q(Decidable.of_not_not $h')
  | ~q(¬¬ ($a : Prop)) => do
    let h' : Q(¬¬$a) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $a)
    replace q(Decidable.of_not_not $h')
  | ~q(¬ ((($a : Prop)) -> $b)) => do
    let h' : Q(¬($a -> $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $a)
    replace q(Decidable.not_imp_iff_and_not.mp $h')
  | ~q(¬ (($a : Prop) ↔ $b)) => do
    let h' : Q(¬($a ↔ $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $b)
    replace q(Decidable.not_iff.mp $h')
  | ~q(($a : Prop) ↔ $b) => do
    let h' : Q($a ↔ $b) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $b)
    replace q(Decidable.iff_iff_and_or_not_and_not.mp $h')
  | ~q((((($a : Prop)) -> False) : Prop)) =>
    throwError "distribNot found nothing to work on with negation"
  | ~q((((($a : Prop)) -> $b) : Prop)) => do
    let h' : Q($a -> $b) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $a)
    replace q(Decidable.not_or_of_imp $h')
  | _ => throwError "distribNot found nothing to work on"

中文:
定义 distribNotOnceAt
  签名: (hypFVar : Expr) (g : MVarId)
  定义体: g.withContext do
  let .fvar fvarId := hypFVar | throwError "not fvar {hypFVar}"
  let h ← fvarId.getDecl
  let e : Q(Prop) ← (do guard <| ← Meta.isProp h.type; pure h.type)
  let replace (p : Expr) : MetaM AssertAfterResult := do
    commitIfNoEx do
      let result ← g.assertAfter fvarId h.userName (← inferType p) p
      /-
        We attempt to clear the old hypothesis. Doing so is crucial for
        avoiding infinite loops. On failure, we roll back the MetaM state
        and ignore this hypothesis. See
        https://github.com/leanprover-community/mathlib4/issues/10590.
      -/
      let newGoal ← result.mvarId.clear fvarId
      return { result with mvarId := newGoal }

  match e with
  | ~q(¬ ($a : Prop) = $b) => do
    let h' : Q(¬$a = $b) := h.toExpr
    replace q(mt propext $h')
  | ~q(($a : Prop) = $b) => do
    let h' : Q($a = $b) := h.toExpr
    replace q(Eq.to_iff $h')
  | ~q(¬ (($a : Prop) ∧ $b)) => do
    let h' : Q(¬($a ∧ $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $b)
    replace q(Decidable.not_and_iff_not_or_not'.mp $h')
  | ~q(¬ (($a : Prop) ∨ $b)) => do
    let h' : Q(¬($a ∨ $b)) := h.toExpr
    replace q(not_or.mp $h')
  | ~q(¬ (($a : Prop) != $b)) => do
    let h' : Q(¬($a != $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable ($a = $b))
    replace q(Decidable.of_not_not $h')
  | ~q(¬¬ ($a : Prop)) => do
    let h' : Q(¬¬$a) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $a)
    replace q(Decidable.of_not_not $h')
  | ~q(¬ ((($a : Prop)) -> $b)) => do
    let h' : Q(¬($a -> $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $a)
    replace q(Decidable.not_imp_iff_and_not.mp $h')
  | ~q(¬ (($a : Prop) ↔ $b)) => do
    let h' : Q(¬($a ↔ $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $b)
    replace q(Decidable.not_iff.mp $h')
  | ~q(($a : Prop) ↔ $b) => do
    let h' : Q($a ↔ $b) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $b)
    replace q(Decidable.iff_iff_and_or_not_and_not.mp $h')
  | ~q((((($a : Prop)) -> False) : Prop)) =>
    throwError "distribNot found nothing to work on with negation"
  | ~q((((($a : Prop)) -> $b) : Prop)) => do
    let h' : Q($a -> $b) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $a)
    replace q(Decidable.not_or_of_imp $h')
  | _ => throwError "distribNot found nothing to work on"

Depends on / 依赖: g.withContext, withContext
-/
def distribNotOnceAt (hypFVar : Expr) (g : MVarId) : MetaM AssertAfterResult := g.withContext do
  let .fvar fvarId := hypFVar | throwError "not fvar {hypFVar}"
  let h ← fvarId.getDecl
  let e : Q(Prop) ← (do guard <| ← Meta.isProp h.type; pure h.type)
  let replace (p : Expr) : MetaM AssertAfterResult := do
    commitIfNoEx do
      let result ← g.assertAfter fvarId h.userName (← inferType p) p
      /-
        We attempt to clear the old hypothesis. Doing so is crucial for
        avoiding infinite loops. On failure, we roll back the MetaM state
        and ignore this hypothesis. See
        https://github.com/leanprover-community/mathlib4/issues/10590.
      -/
      let newGoal ← result.mvarId.clear fvarId
      return { result with mvarId := newGoal }

  match e with
  | ~q(¬ ($a : Prop) = $b) => do
    let h' : Q(¬$a = $b) := h.toExpr
    replace q(mt propext $h')
  | ~q(($a : Prop) = $b) => do
    let h' : Q($a = $b) := h.toExpr
    replace q(Eq.to_iff $h')
  | ~q(¬ (($a : Prop) ∧ $b)) => do
    let h' : Q(¬($a ∧ $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $b)
    replace q(Decidable.not_and_iff_not_or_not'.mp $h')
  | ~q(¬ (($a : Prop) ∨ $b)) => do
    let h' : Q(¬($a ∨ $b)) := h.toExpr
    replace q(not_or.mp $h')
  | ~q(¬ (($a : Prop) != $b)) => do
    let h' : Q(¬($a != $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable ($a = $b))
    replace q(Decidable.of_not_not $h')
  | ~q(¬¬ ($a : Prop)) => do
    let h' : Q(¬¬$a) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $a)
    replace q(Decidable.of_not_not $h')
  | ~q(¬ ((($a : Prop)) -> $b)) => do
    let h' : Q(¬($a -> $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $a)
    replace q(Decidable.not_imp_iff_and_not.mp $h')
  | ~q(¬ (($a : Prop) ↔ $b)) => do
    let h' : Q(¬($a ↔ $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $b)
    replace q(Decidable.not_iff.mp $h')
  | ~q(($a : Prop) ↔ $b) => do
    let h' : Q($a ↔ $b) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $b)
    replace q(Decidable.iff_iff_and_or_not_and_not.mp $h')
  | ~q((((($a : Prop)) -> False) : Prop)) =>
    throwError "distribNot found nothing to work on with negation"
  | ~q((((($a : Prop)) -> $b) : Prop)) => do
    let h' : Q($a -> $b) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $a)
    replace q(Decidable.not_or_of_imp $h')
  | _ => throwError "distribNot found nothing to work on"

/--
Definition of `DistribNotState` / `DistribNotState` 的定义

English:
structure DistribNotState
  parameters: where
  axioms and operations (2):
    - fvars : List Expr
    - currentGoal : MVarId

中文:
结构 DistribNotState
  参数: where
  公理与运算 (2 个):
    - fvars : 列表 Expr
    - currentGoal : MVarId

Depends on / 依赖: currentGoal, distribNotAt, distribNotOnceAt, fvarId, fvs.map, mkFVar, mvarId, nIters, newFVars, result, result.fvarId, result.mvarId, result.subst.apply, state.currentGoal, state.fvars
-/
structure DistribNotState where
  /-- The list of hypothesis left to work on, renamed to be up-to-date with
  the current goal. -/
  fvars : List Expr

  /-- The current goal. -/
  currentGoal : MVarId

/--
Definition of `distribNotAt` / `distribNotAt` 的定义

English:
definition distribNotAt
  signature: (nIters : Nat) (state : DistribNotState)
  body: match nIters, state.fvars with
  | 0, _ | _, [] => pure state
  | n + 1, fv::fvs => do
    try
      let result ← distribNotOnceAt fv state.currentGoal
      let newFVars := mkFVar result.fvarId :: fvs.map (fun x => result.subst.apply x)
      distribNotAt n ⟨newFVars, result.mvarId⟩
    catch _ => pure state

中文:
定义 distribNotAt
  签名: (nIters : 自然数) (state : DistribNotState)
  定义体: match nIters, state.fvars with
  | 0, _ | _, [] => pure state
  | n + 1, fv::fvs => do
    try
      let result ← distribNotOnceAt fv state.currentGoal
      let newFVars := mkFVar result.fvarId :: fvs.map (fun x => result.subst.apply x)
      distribNotAt n ⟨newFVars, result.mvarId⟩
    catch _ => pure state
-/
partial def distribNotAt (nIters : Nat) (state : DistribNotState) : MetaM DistribNotState :=
  match nIters, state.fvars with
  | 0, _ | _, [] => pure state
  | n + 1, fv::fvs => do
    try
      let result ← distribNotOnceAt fv state.currentGoal
      let newFVars := mkFVar result.fvarId :: fvs.map (fun x => result.subst.apply x)
      distribNotAt n ⟨newFVars, result.mvarId⟩
    catch _ => pure state

/--
Definition of `distribNotAux` / `distribNotAux` 的定义

English:
definition distribNotAux
  signature: (fvars : List Expr) (g : MVarId)
  body: match fvars with
  | [] => pure g
  | _ => do
    let result ← distribNotAt 3 ⟨fvars, g⟩
    distribNotAux result.fvars.tail! result.currentGoal

中文:
定义 distribNotAux
  签名: (fvars : 列表 Expr) (g : MVarId)
  定义体: match fvars with
  | [] => pure g
  | _ => do
    let result ← distribNotAt 3 ⟨fvars, g⟩
    distribNotAux result.fvars.tail! result.currentGoal
-/
partial def distribNotAux (fvars : List Expr) (g : MVarId) : MetaM MVarId :=
  match fvars with
  | [] => pure g
  | _ => do
    let result ← distribNotAt 3 ⟨fvars, g⟩
    distribNotAux result.fvars.tail! result.currentGoal

/--
Definition of `distribNot` / `distribNot` 的定义

English:
definition distribNot
  signature: : TacticM Unit
  body: withMainContext do
  let mut fvars := []
  for h in ← getLCtx do
    if !h.isImplementationDetail then
      fvars := mkFVar h.fvarId :: fvars
  liftMetaTactic' (distribNotAux fvars)

中文:
定义 distribNot
  签名: : TacticM 单元
  定义体: withMainContext do
  let mut fvars := []
  for h in ← getLCtx do
    if !h.isImplementationDetail then
      fvars := mkFVar h.fvarId :: fvars
  liftMetaTactic' (distribNotAux fvars)

Depends on / 依赖: withMainContext
-/
def distribNot : TacticM Unit := withMainContext do
  let mut fvars := []
  for h in ← getLCtx do
    if !h.isImplementationDetail then
      fvars := mkFVar h.fvarId :: fvars
  liftMetaTactic' (distribNotAux fvars)

/--
Definition of `Config` / `Config` 的定义

English:
structure Config
  (no additional axioms)

中文:
结构 余nfig
  (无附加公理)
-/
structure Config

/-- Function elaborating `Config`. -/
declare_config_elab elabConfig Config

/--
Definition of `coreConstructorMatcher` / `coreConstructorMatcher` 的定义

English:
definition coreConstructorMatcher
  signature: (e : Q(Prop))
  body: match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ↔ _) => pure true
  | ~q(True) => pure true
  | _ => pure false

中文:
定义 coreConstructorMatcher
  签名: (e : Q(命题))
  定义体: match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ↔ _) => pure true
  | ~q(True) => pure true
  | _ => pure false
-/
def coreConstructorMatcher (e : Q(Prop)) : MetaM Bool :=
  match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ↔ _) => pure true
  | ~q(True) => pure true
  | _ => pure false

/--
Definition of `casesMatcher` / `casesMatcher` 的定义

English:
definition casesMatcher
  signature: (e : Q(Prop))
  body: match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ∨ _) => pure true
  | ~q(Exists _) => pure true
  | ~q(False) => pure true
  | _ => pure false

@[inherit_doc]
local infixl: 50 " <;> " => andThenOnSubgoals

中文:
定义 casesMatcher
  签名: (e : Q(命题))
  定义体: match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ∨ _) => pure true
  | ~q(Exists _) => pure true
  | ~q(False) => pure true
  | _ => pure false

@[inherit_doc]
local infixl: 50 " <;> " => andThenOnSubgoals

Depends on / 依赖: Exists
-/
def casesMatcher (e : Q(Prop)) : MetaM Bool :=
  match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ∨ _) => pure true
  | ~q(Exists _) => pure true
  | ~q(False) => pure true
  | _ => pure false

@[inherit_doc]
local infixl: 50 " <;> " => andThenOnSubgoals

/--
Definition of `tautoCore` / `tautoCore` 的定义

English:
definition tautoCore
  signature: : TacticM Unit
  body: do
  _ ← tryTactic (evalTactic (← `(tactic| contradiction)))
  _ ← tryTactic (evalTactic (← `(tactic| assumption)))
  iterateUntilFailure do
    let gs ← getUnsolvedGoals
    allGoals (
      liftMetaTactic (fun m => do pure [(← m.intros!).2]) <;>
      distribNot <;>
      liftMetaTactic (casesMatching casesMatcher (recursive := true) (throwOnNoMatch := false)) <;>
      (do _ ← tryTactic (evalTactic (← `(tactic| contradiction)))) <;>
      (do _ ← tryTactic (evalTactic (← `(tactic| refine or_iff_not_imp_left.mpr ?_)))) <;>
      liftMetaTactic (fun m => do pure [(← m.intros!).2]) <;>
      liftMetaTactic (constructorMatching · coreConstructorMatcher
        (recursive := true) (throwOnNoMatch := false)) <;>
      do _ ← tryTactic (evalTactic (← `(tactic| assumption))))
    let gs' ← getUnsolvedGoals
    if gs == gs' then failure -- no progress
    pure ()

中文:
定义 tautoCore
  签名: : TacticM 单元
  定义体: do
  _ ← tryTactic (evalTactic (← `(tactic| contradiction)))
  _ ← tryTactic (evalTactic (← `(tactic| assumption)))
  iterateUntilFailure do
    let gs ← getUnsolvedGoals
    allGoals (
      liftMetaTactic (fun m => do pure [(← m.intros!).2]) <;>
      distribNot <;>
      liftMetaTactic (casesMatching casesMatcher (recursive := true) (throwOnNoMatch := false)) <;>
      (do _ ← tryTactic (evalTactic (← `(tactic| contradiction)))) <;>
      (do _ ← tryTactic (evalTactic (← `(tactic| refine or_iff_not_imp_left.mpr ?_)))) <;>
      liftMetaTactic (fun m => do pure [(← m.intros!).2]) <;>
      liftMetaTactic (constructorMatching · coreConstructorMatcher
        (recursive := true) (throwOnNoMatch := false)) <;>
      do _ ← tryTactic (evalTactic (← `(tactic| assumption))))
    let gs' ← getUnsolvedGoals
    if gs == gs' then failure -- no progress
    pure ()
-/
def tautoCore : TacticM Unit := do
  _ ← tryTactic (evalTactic (← `(tactic| contradiction)))
  _ ← tryTactic (evalTactic (← `(tactic| assumption)))
  iterateUntilFailure do
    let gs ← getUnsolvedGoals
    allGoals (
      liftMetaTactic (fun m => do pure [(← m.intros!).2]) <;>
      distribNot <;>
      liftMetaTactic (casesMatching casesMatcher (recursive := true) (throwOnNoMatch := false)) <;>
      (do _ ← tryTactic (evalTactic (← `(tactic| contradiction)))) <;>
      (do _ ← tryTactic (evalTactic (← `(tactic| refine or_iff_not_imp_left.mpr ?_)))) <;>
      liftMetaTactic (fun m => do pure [(← m.intros!).2]) <;>
      liftMetaTactic (constructorMatching · coreConstructorMatcher
        (recursive := true) (throwOnNoMatch := false)) <;>
      do _ ← tryTactic (evalTactic (← `(tactic| assumption))))
    let gs' ← getUnsolvedGoals
    if gs == gs' then failure -- no progress
    pure ()

/--
Definition of `finishingConstructorMatcher` / `finishingConstructorMatcher` 的定义

English:
definition finishingConstructorMatcher
  signature: (e : Q(Prop))
  body: match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ↔ _) => pure true
  | ~q(Exists _) => pure true
  | ~q(True) => pure true
  | _ => pure false

中文:
定义 finishingConstructorMatcher
  签名: (e : Q(命题))
  定义体: match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ↔ _) => pure true
  | ~q(Exists _) => pure true
  | ~q(True) => pure true
  | _ => pure false

Depends on / 依赖: Exists
-/
def finishingConstructorMatcher (e : Q(Prop)) : MetaM Bool :=
  match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ↔ _) => pure true
  | ~q(Exists _) => pure true
  | ~q(True) => pure true
  | _ => pure false

/--
Definition of `tautology` / `tautology` 的定义

English:
definition tautology
  signature: : TacticM Unit
  body: focus do
  classical do
    let g ← getMainGoal
    tautoCore
    allGoals (iterateUntilFailure
      (evalTactic (← `(tactic| rfl)) <|>
evalTactic (← `(tactic| solve_by_elim)) >
      liftMetaTactic (constructorMatching · finishingConstructorMatcher)))
    unless (← getUnsolvedGoals).isEmpty do
      throwTacticEx `tauto g

中文:
定义 tautology
  签名: : TacticM 单元
  定义体: focus do
  classical do
    let g ← getMainGoal
    tautoCore
    allGoals (iterateUntilFailure
      (evalTactic (← `(tactic| rfl)) <|>
evalTactic (← `(tactic| solve_by_elim)) >
      liftMetaTactic (constructorMatching · finishingConstructorMatcher)))
    unless (← getUnsolvedGoals).isEmpty do
      throwTacticEx `tauto g
-/
def tautology : TacticM Unit := focus do
  classical do
    let g ← getMainGoal
    tautoCore
    allGoals (iterateUntilFailure
      (evalTactic (← `(tactic| rfl)) <|>
evalTactic (← `(tactic| solve_by_elim)) >
      liftMetaTactic (constructorMatching · finishingConstructorMatcher)))
    unless (← getUnsolvedGoals).isEmpty do
      throwTacticEx `tauto g

/--
`tauto` proves tautologies in classical propositional logic.
It breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
using `rfl`, `contradiction` or `solve_by_elim`.
This is a finishing tactic: it either closes the goal or raises an error.

This tactic makes no attempt to avoid classical reasoning. The `itauto` tactic
is designed for that purpose.
-/
syntax (name := tauto) "tauto" optConfig : tactic

elab_rules : tactic | `(tactic| tauto $cfg:optConfig) => do
  let _cfg ← elabConfig cfg
  tautology

end Mathlib.Tactic.Tauto

open Mathlib.TacticAnalysis

/-- Report places where `tauto` can be replaced by `grind`. -/
register_option linter.tacticAnalysis.tautoToGrind : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.tautoToGrind,
  inherit_doc linter.tacticAnalysis.tautoToGrind]
/--
Definition of `tautoToGrind` / `tautoToGrind` 的定义

English:
definition tautoToGrind
  body: terminalReplacement "tauto" "grind" ``Mathlib.Tactic.Tauto.tauto (fun _ _ _ => `(tactic| grind))
    (reportSuccess := true) (reportFailure := false)

中文:
定义 tautoToGrind
  定义体: terminalReplacement "tauto" "grind" ``Mathlib.Tactic.Tauto.tauto (fun _ _ _ => `(tactic| grind))
    (reportSuccess := true) (reportFailure := false)

Depends on / 依赖: Mathlib, Mathlib.Tactic.Tauto.tauto, Tactic, reportFailure, reportSuccess, tactic, terminalReplacement
-/
def tautoToGrind :=
  terminalReplacement "tauto" "grind" ``Mathlib.Tactic.Tauto.tauto (fun _ _ _ => `(tactic| grind))
    (reportSuccess := true) (reportFailure := false)

/-- Debug `grind` by identifying places where it does not yet supersede `tauto`. -/
register_option linter.tacticAnalysis.regressions.tautoToGrind : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.regressions.tautoToGrind,
  inherit_doc linter.tacticAnalysis.regressions.tautoToGrind]
/--
Definition of `tautoToGrindRegressions` / `tautoToGrindRegressions` 的定义

English:
definition tautoToGrindRegressions
  body: grindReplacementWith "tauto" `Mathlib.Tactic.Tauto.tauto

中文:
定义 tautoToGrindRegressions
  定义体: grindReplacementWith "tauto" `Mathlib.Tactic.Tauto.tauto

Depends on / 依赖: Mathlib, Mathlib.Tactic.Tauto.tauto, Tactic, grindReplacementWith
-/
def tautoToGrindRegressions := grindReplacementWith "tauto" `Mathlib.Tactic.Tauto.tauto
