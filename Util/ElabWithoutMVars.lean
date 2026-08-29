/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Init

/-!
# `elabTermWithoutNewMVars`

-/

public meta section

open Lean Elab Tactic

/--
Definition of `elabTermWithoutNewMVars` / `elabTermWithoutNewMVars` 的定义

English:
definition elabTermWithoutNewMVars
  signature: (tactic : Name) (t : Term)
  body: Term.withoutErrToSorry do
  let (e, mvars) ← elabTermWithHoles t none tactic
  unless mvars.isEmpty do
    throwErrorAt t "Argument passed to {tactic} has metavariables:{indentD e}"
  return e

中文:
定义 elabTermWithoutNewMVars
  签名: (tactic : Name) (t : Term)
  定义体: Term.withoutErrToSorry do
  let (e, mvars) ← elabTermWithHoles t none tactic
  unless mvars.isEmpty do
    throwErrorAt t "Argument passed to {tactic} has metavariables:{indentD e}"
  return e

Depends on / 依赖: Term.withoutErrToSorry, withoutErrToSorry
-/
def elabTermWithoutNewMVars (tactic : Name) (t : Term) : TacticM Expr := Term.withoutErrToSorry do
  let (e, mvars) ← elabTermWithHoles t none tactic
  unless mvars.isEmpty do
    throwErrorAt t "Argument passed to {tactic} has metavariables:{indentD e}"
  return e
