/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.Tactic.CategoryTheory.Coherence.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Normalize
public import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence

/-!
# `monoidal` tactic

This file provides `monoidal` tactic, which solves equations in a monoidal category, where
the two sides only differ by replacing strings of monoidal structural morphisms (that is,
associators, unitors, and identities) with different strings of structural morphisms with the same
source and target. In other words, `monoidal` solves equalities where both sides have the same
string diagrams.

The core function for the `monoidal` tactic is provided in
`Mathlib/Tactic/CategoryTheory/Coherence/Basic.lean`. See this file for more details about the
implementation.

-/

public meta section

open Lean Meta Elab Tactic
open CategoryTheory Mathlib.Tactic.BicategoryLike

namespace Mathlib.Tactic.Monoidal

/--
Definition of `monoidalNf` / `monoidalNf` 的定义

English:
definition monoidalNf
  signature: (mvarId : MVarId)
  body: do
  BicategoryLike.normalForm Monoidal.Context `monoidal mvarId

@[inherit_doc monoidalNf]

中文:
定义 monoidalNf
  签名: (mvarId : MVarId)
  定义体: do
  BicategoryLike.normalForm Monoidal.Context `monoidal mvarId

@[inherit_doc monoidalNf]
-/
def monoidalNf (mvarId : MVarId) : MetaM (List MVarId) := do
  BicategoryLike.normalForm Monoidal.Context `monoidal mvarId

@[inherit_doc monoidalNf]
elab "monoidal_nf" : tactic => withMainContext do
  replaceMainGoal (← monoidalNf (← getMainGoal))

/--
Definition of `monoidal` / `monoidal` 的定义

English:
definition monoidal
  signature: (mvarId : MVarId)
  body: BicategoryLike.main Monoidal.Context `monoidal mvarId

@[inherit_doc monoidal]

中文:
定义 monoidal
  签名: (mvarId : MVarId)
  定义体: BicategoryLike.main Monoidal.Context `monoidal mvarId

@[inherit_doc monoidal]

Depends on / 依赖: BicategoryLike, BicategoryLike.main, Context, Monoidal, Monoidal.Context, monoidal, mvarId
-/
def monoidal (mvarId : MVarId) : MetaM (List MVarId) :=
  BicategoryLike.main Monoidal.Context `monoidal mvarId

@[inherit_doc monoidal]
elab "monoidal" : tactic => withMainContext do
replaceMainGoal ← monoidal ← getMainGoal

end Mathlib.Tactic.Monoidal
