/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.Tactic.CategoryTheory.Bicategory.Normalize
public import Mathlib.Tactic.CategoryTheory.Bicategory.PureCoherence
public import Mathlib.Tactic.CategoryTheory.Coherence.Basic

/-!
# `bicategory` tactic

This file provides `bicategory` tactic, which solves equations in a bicategory, where
the two sides only differ by replacing strings of bicategory structural morphisms (that is,
associators, unitors, and identities) with different strings of structural morphisms with the same
source and target. In other words, `bicategory` solves equalities where both sides have the same
string diagrams.

The core function for the `bicategory` tactic is provided in
`Mathlib/Tactic/CategoryTheory/Coherence/Basic.lean`. See this file for more details about the
implementation.

-/

public meta section

open Lean Meta Elab Tactic
open CategoryTheory Mathlib.Tactic.BicategoryLike

namespace Mathlib.Tactic.Bicategory

/--
Definition of `bicategoryNf` / `bicategoryNf` 的定义

English:
definition bicategoryNf
  signature: (mvarId : MVarId)
  body: do
  BicategoryLike.normalForm Bicategory.Context `bicategory mvarId

@[inherit_doc bicategoryNf]

中文:
定义 bicategoryNf
  签名: (mvarId : MVarId)
  定义体: do
  BicategoryLike.normalForm Bicategory.Context `bicategory mvarId

@[inherit_doc bicategoryNf]
-/
def bicategoryNf (mvarId : MVarId) : MetaM (List MVarId) := do
  BicategoryLike.normalForm Bicategory.Context `bicategory mvarId

@[inherit_doc bicategoryNf]
elab "bicategory_nf" : tactic => withMainContext do
  replaceMainGoal (← bicategoryNf (← getMainGoal))

/--
Definition of `bicategory` / `bicategory` 的定义

English:
definition bicategory
  signature: (mvarId : MVarId)
  body: BicategoryLike.main Bicategory.Context `bicategory mvarId

@[inherit_doc bicategory]

中文:
定义 bicategory
  签名: (mvarId : MVarId)
  定义体: BicategoryLike.main Bicategory.Context `bicategory mvarId

@[inherit_doc bicategory]

Depends on / 依赖: Bicategory, Bicategory.Context, BicategoryLike, BicategoryLike.main, Context, bicategory, mvarId
-/
def bicategory (mvarId : MVarId) : MetaM (List MVarId) :=
  BicategoryLike.main Bicategory.Context `bicategory mvarId

@[inherit_doc bicategory]
elab "bicategory" : tactic => withMainContext do
replaceMainGoal ← bicategory ← getMainGoal

end Mathlib.Tactic.Bicategory
