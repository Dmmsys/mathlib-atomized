/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.Basic
public import Qq
public import Qq.Typ

/-!
# `SynthesizeUsing`

This is a slight simplification of the `solve_aux` tactic in Lean3.
-/

public meta section

open Lean Elab Tactic Meta Qq

-- In Lean3 this was called `solve_aux`,
-- and took a `TacticM α` and captured the produced value in `α`.
-- As this was barely used, we've simplified here.
/--
Definition of `synthesizeUsing` / `synthesizeUsing` 的定义

English:
definition synthesizeUsing
  signature: {u : Level} (type : Q(Sort u)) (tac : TacticM Unit)
  body: do
  let m ← mkFreshExprMVar type
  let goals ← (Term.withoutErrToSorry <| run m.mvarId! tac).run'
  return (goals, ← instantiateMVars m)

中文:
定义 synthesizeUsing
  签名: {u : Level} (type : Q(类型层 u)) (tac : TacticM 单元)
  定义体: do
  let m ← mkFreshExprMVar type
  let goals ← (Term.withoutErrToSorry <| run m.mvarId! tac).run'
  return (goals, ← instantiateMVars m)
-/
def synthesizeUsing {u : Level} (type : Q(Sort u)) (tac : TacticM Unit) :
    MetaM (List MVarId × Q($type)) := do
  let m ← mkFreshExprMVar type
  let goals ← (Term.withoutErrToSorry <| run m.mvarId! tac).run'
  return (goals, ← instantiateMVars m)

/--
Definition of `synthesizeUsing'` / `synthesizeUsing'` 的定义

English:
definition synthesizeUsing'
  signature: {u : Level} (type : Q(Sort u)) (tac : TacticM Unit)
  body: do
  let (goals, e) ← synthesizeUsing type tac
  -- Note: does not use `tac *> Tactic.done` since that just adds a message
  -- rather than raising an error.
  unless goals.isEmpty do
    throwError m!"synthesizeUsing': unsolved goals\n{goalsToMessageData goals}"
  return e

中文:
定义 synthesizeUsing'
  签名: {u : Level} (type : Q(类型层 u)) (tac : TacticM 单元)
  定义体: do
  let (goals, e) ← synthesizeUsing type tac
  -- Note: does not use `tac *> Tactic.done` since that just adds a message
  -- rather than raising an error.
  unless goals.isEmpty do
    throwError m!"synthesizeUsing': unsolved goals\n{goalsToMessageData goals}"
  return e
-/
def synthesizeUsing' {u : Level} (type : Q(Sort u)) (tac : TacticM Unit) : MetaM Q($type) := do
  let (goals, e) ← synthesizeUsing type tac
  -- Note: does not use `tac *> Tactic.done` since that just adds a message
  -- rather than raising an error.
  unless goals.isEmpty do
    throwError m!"synthesizeUsing': unsolved goals\n{goalsToMessageData goals}"
  return e

/--
Definition of `synthesizeUsingTactic` / `synthesizeUsingTactic` 的定义

English:
definition synthesizeUsingTactic
  signature: {u : Level} (type : Q(Sort u)) (tac : Syntax)
  body: do
  synthesizeUsing type (do evalTactic tac)

中文:
定义 synthesizeUsingTactic
  签名: {u : Level} (type : Q(类型层 u)) (tac : Syntax)
  定义体: do
  synthesizeUsing type (do evalTactic tac)
-/
def synthesizeUsingTactic {u : Level} (type : Q(Sort u)) (tac : Syntax) :
    MetaM (List MVarId × Q($type)) := do
  synthesizeUsing type (do evalTactic tac)

/--
Definition of `synthesizeUsingTactic'` / `synthesizeUsingTactic'` 的定义

English:
definition synthesizeUsingTactic'
  signature: {u : Level} (type : Q(Sort u)) (tac : Syntax)
  body: do
  synthesizeUsing' type (do evalTactic tac)

中文:
定义 synthesizeUsingTactic'
  签名: {u : Level} (type : Q(类型层 u)) (tac : Syntax)
  定义体: do
  synthesizeUsing' type (do evalTactic tac)
-/
def synthesizeUsingTactic' {u : Level} (type : Q(Sort u)) (tac : Syntax) : MetaM Q($type) := do
  synthesizeUsing' type (do evalTactic tac)
