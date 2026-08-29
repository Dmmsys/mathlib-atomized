/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Countable.Small
public import Mathlib.Data.Fintype.EquivFin

/-!
# Fintype instance for `Shrink`
-/

public section

universe u v
variable {α : Type u} [Fintype α]

/--
Instance `Shrink.instFintype` / 实例 `Shrink.instFintype`

English:
instance Shrink.instFintype
  signature: : Fintype (Shrink.{v} α)
  body: .ofEquiv _ (equivShrink _)

中文:
实例 Shrink.instFintype
  签名: : Fintype (Shrink.{v} α)
  定义体: .ofEquiv _ (equivShrink _)

Depends on / 依赖: equivShrink, ofEquiv
-/
noncomputable instance Shrink.instFintype : Fintype (Shrink.{v} α) := .ofEquiv _ (equivShrink _)

/--
Instance `Shrink.instFinite` / 实例 `Shrink.instFinite`

English:
instance Shrink.instFinite
  signature: {α : Type u} [Finite α]
  body: .of_equiv _ (equivShrink _)

中文:
实例 Shrink.instFinite
  签名: {α : 类型u} [Finite α]
  定义体: .of_equiv _ (equivShrink _)

Depends on / 依赖: equivShrink, of_equiv
-/
instance Shrink.instFinite {α : Type u} [Finite α] : Finite (Shrink.{v} α) :=
  .of_equiv _ (equivShrink _)

/--
lemma `Fintype.card_shrink` / 引理 `Fintype.card_shrink`

English:
lemma Fintype.card_shrink
  given: [Fintype (Shrink.{v} α)]
  statement: card (Shrink.{v} α) = card α
  proof: card_congr (equivShrink _).symm

中文:
引理 Fintype.card_shrink
  条件: [Fintype (Shrink.{v} α)]
  结论: card (Shrink.{v} α) = card α
  证明: card_congr (equivShrink _).symm
-/
@[simp] lemma Fintype.card_shrink [Fintype (Shrink.{v} α)] : card (Shrink.{v} α) = card α :=
  card_congr (equivShrink _).symm
