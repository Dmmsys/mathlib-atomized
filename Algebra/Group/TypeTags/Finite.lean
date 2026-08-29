/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Fintype.Card

/-!
# `Finite`, `Infinite` and `Fintype` are preserved by `Additive` and `Multiplicative`.
-/

public section

assert_not_exists MonoidWithZero MulAction

universe u

variable {α : Type u}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] : Finite (Additive α)
  body: Finite.of_equiv α (by rfl)

中文:
实例 [有限
  签名: α] : 有限 (加性 α)
  定义体: Finite.of_equiv α (by rfl)

Depends on / 依赖: Finite, Finite.of_equiv, of_equiv
-/
instance [Finite α] : Finite (Additive α) :=
  Finite.of_equiv α (by rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] : Finite (Multiplicative α)
  body: Finite.of_equiv α (by rfl)

中文:
实例 [有限
  签名: α] : 有限 (Multiplicative α)
  定义体: Finite.of_equiv α (by rfl)

Depends on / 依赖: Finite, Finite.of_equiv, of_equiv
-/
instance [Finite α] : Finite (Multiplicative α) :=
  Finite.of_equiv α (by rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Infinite α] : Infinite (Additive α)
  body: h

中文:
实例 [h
  签名: : 无限 α] : 无限 (加性 α)
  定义体: h
-/
instance [h : Infinite α] : Infinite (Additive α) := h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Infinite α] : Infinite (Multiplicative α)
  body: h

中文:
实例 [h
  签名: : 无限 α] : 无限 (Multiplicative α)
  定义体: h
-/
instance [h : Infinite α] : Infinite (Multiplicative α) := h

/--
Instance `Additive.fintype` / 实例 `Additive.fintype`

English:
instance Additive.fintype
  signature: : forall [Fintype α], Fintype (Additive α)
  body: Fintype.ofEquiv α Additive.ofMul

中文:
实例 加性.fintype
  签名: : 对任意 [有限类型 α], 有限类型 (加性 α)
  定义体: Fintype.ofEquiv α Additive.ofMul

Depends on / 依赖: Additive, Additive.ofMul, Fintype, Fintype.ofEquiv, ofEquiv
-/
instance Additive.fintype : forall [Fintype α], Fintype (Additive α) :=
  Fintype.ofEquiv α Additive.ofMul

/--
Instance `Multiplicative.fintype` / 实例 `Multiplicative.fintype`

English:
instance Multiplicative.fintype
  signature: : forall [Fintype α], Fintype (Multiplicative α)
  body: Fintype.ofEquiv α Multiplicative.ofAdd

中文:
实例 Multiplicative.fintype
  签名: : 对任意 [有限类型 α], 有限类型 (Multiplicative α)
  定义体: Fintype.ofEquiv α Multiplicative.ofAdd

Depends on / 依赖: Fintype, Fintype.ofEquiv, Multiplicative, Multiplicative.ofAdd, ofEquiv
-/
instance Multiplicative.fintype : forall [Fintype α], Fintype (Multiplicative α) :=
  Fintype.ofEquiv α Multiplicative.ofAdd

/--
lemma `Fintype.card_multiplicative` / 引理 `Fintype.card_multiplicative`

English:
lemma Fintype.card_multiplicative
  given: (α : Type*) [Fintype α]
  proof: Finset.card_map _

中文:
引理 有限类型.card_multiplicative
  条件: (α : 类型) [有限类型 α]
  证明: Finset.card_map _
-/
@[simp] lemma Fintype.card_multiplicative (α : Type*) [Fintype α] :
    card (Multiplicative α) = card α := Finset.card_map _

/--
lemma `Fintype.card_additive` / 引理 `Fintype.card_additive`

English:
lemma Fintype.card_additive
  given: (α : Type*) [Fintype α]
  statement: card (Additive α) = card α
  proof: Finset.card_map _

中文:
引理 有限类型.card_additive
  条件: (α : 类型) [有限类型 α]
  结论: card (加性 α) = card α
  证明: Finset.card_map _
-/
@[simp] lemma Fintype.card_additive (α : Type*) [Fintype α] : card (Additive α) = card α :=
  Finset.card_map _
