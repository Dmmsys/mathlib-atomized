/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen, Kim Morrison
-/
module

public meta import Lean.Elab.Tactic.Conv.Basic
public import Mathlib.Init

/-!
## Introduce the `apply_congr` conv mode tactic.

`apply_congr` will apply congruence lemmas inside `conv` mode.
It is particularly useful when the automatically generated congruence lemmas
are not of the optimal shape. An example, described in the doc-string is
rewriting inside the operand of a `Finset.sum`.
-/

public meta section

open Lean Expr Parser.Tactic Elab Elab.Tactic Meta Conv

/--
Definition of `Lean.Elab.Tactic.applyCongr` / `Lean.Elab.Tactic.applyCongr` 的定义

English:
definition Lean.Elab.Tactic.applyCongr
  signature: (q : Option Expr)
  body: do
let const lhsFun _ ← (getAppFn ∘ cleanupAnnotations) < > instantiateMVars (← getLhs) |
    throwError "Left-hand side must be an application of a constant."
  let congrTheoremExprs ←
    match q with
    -- If the user specified a lemma, use that one,
    | some e =>
      pure [e]
    -- otherwise, look up everything tagged `@[congr]`
    | none =>
      let congrTheorems ←
(fun congrTheoremMap => congrTheoremMap.get lhsFun) < > getSimpCongrTheorems
      congrTheorems.mapM (fun congrTheorem =>
liftM mkConstWithFreshMVarLevels congrTheorem.theoremName)
  if congrTheoremExprs == [] then
    throwError "No matching congr lemmas found"
  -- For every lemma:
  liftMetaTactic fun mainGoal => congrTheoremExprs.firstM (fun congrTheoremExpr => do
    let newGoals ← mainGoal.apply congrTheoremExpr { newGoals := .nonDependentOnly }
newGoals.mapM fun newGoal => Prod.snd < > newGoal.intros)

中文:
定义 Lean.Elab.Tactic.applyCongr
  签名: (q : 选项类型 Expr)
  定义体: do
let const lhsFun _ ← (getAppFn ∘ cleanupAnnotations) < > instantiateMVars (← getLhs) |
    throwError "Left-hand side must be an application of a constant."
  let congrTheoremExprs ←
    match q with
    -- If the user specified a lemma, use that one,
    | some e =>
      pure [e]
    -- otherwise, look up everything tagged `@[congr]`
    | none =>
      let congrTheorems ←
(fun congrTheoremMap => congrTheoremMap.get lhsFun) < > getSimpCongrTheorems
      congrTheorems.mapM (fun congrTheorem =>
liftM mkConstWithFreshMVarLevels congrTheorem.theoremName)
  if congrTheoremExprs == [] then
    throwError "No matching congr lemmas found"
  -- For every lemma:
  liftMetaTactic fun mainGoal => congrTheoremExprs.firstM (fun congrTheoremExpr => do
    let newGoals ← mainGoal.apply congrTheoremExpr { newGoals := .nonDependentOnly }
newGoals.mapM fun newGoal => Prod.snd < > newGoal.intros)
-/
def Lean.Elab.Tactic.applyCongr (q : Option Expr) : TacticM Unit := do
let const lhsFun _ ← (getAppFn ∘ cleanupAnnotations) < > instantiateMVars (← getLhs) |
    throwError "Left-hand side must be an application of a constant."
  let congrTheoremExprs ←
    match q with
    -- If the user specified a lemma, use that one,
    | some e =>
      pure [e]
    -- otherwise, look up everything tagged `@[congr]`
    | none =>
      let congrTheorems ←
(fun congrTheoremMap => congrTheoremMap.get lhsFun) < > getSimpCongrTheorems
      congrTheorems.mapM (fun congrTheorem =>
liftM mkConstWithFreshMVarLevels congrTheorem.theoremName)
  if congrTheoremExprs == [] then
    throwError "No matching congr lemmas found"
  -- For every lemma:
  liftMetaTactic fun mainGoal => congrTheoremExprs.firstM (fun congrTheoremExpr => do
    let newGoals ← mainGoal.apply congrTheoremExpr { newGoals := .nonDependentOnly }
newGoals.mapM fun newGoal => Prod.snd < > newGoal.intros)

syntax (name := Lean.Parser.Tactic.applyCongr) "apply_congr" (ppSpace colGt term)? : conv

-- TODO: add `apply_congr with h` to specify hypothesis name
-- https://github.com/leanprover-community/mathlib/issues/2882

elab_rules : conv
  | `(conv| apply_congr$[ $t?]?) => do
    let e? ← t?.mapM (fun t => elabTerm t.raw none)
    applyCongr e?
