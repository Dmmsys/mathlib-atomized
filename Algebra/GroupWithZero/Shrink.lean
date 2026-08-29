/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance
public import Mathlib.Algebra.GroupWithZero.TransferInstance

/-!
# Transfer group with zero structures from `α` to `Shrink α`
-/

public section

noncomputable section

universe v
variable {M α : Type*} [Small.{v} α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemigroupWithZero
  signature: α] : SemigroupWithZero (Shrink α)
  body: (equivShrink _).symm.semigroupWithZero

中文:
实例 [带零半群
  签名: α] : 带零半群 (Shrink α)
  定义体: (equivShrink _).symm.semigroupWithZero

Depends on / 依赖: equivShrink, semigroupWithZero, symm.semigroupWithZero
-/
instance [SemigroupWithZero α] : SemigroupWithZero (Shrink α) :=
  (equivShrink _).symm.semigroupWithZero
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: α] : MulZeroClass (Shrink α)
  body: (equivShrink _).symm.mulZeroClass

中文:
实例 [乘零类
  签名: α] : 乘零类 (Shrink α)
  定义体: (equivShrink _).symm.mulZeroClass

Depends on / 依赖: equivShrink, mulZeroClass, symm.mulZeroClass
-/
instance [MulZeroClass α] : MulZeroClass (Shrink α) := (equivShrink _).symm.mulZeroClass
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroOneClass
  signature: α] : MulZeroOneClass (Shrink α)
  body: (equivShrink _).symm.mulZeroOneClass

中文:
实例 [乘零幺类
  签名: α] : 乘零幺类 (Shrink α)
  定义体: (equivShrink _).symm.mulZeroOneClass
-/
instance [MulZeroOneClass α] : MulZeroOneClass (Shrink α) := (equivShrink _).symm.mulZeroOneClass

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [AddCommMonoid α] [DistribMulAction M α] : DistribMulAction M (Shrink.{v} α)
  body: (equivShrink α).symm.distribMulAction M

中文:
实例 [幺半群
  签名: M] [加法交换幺半群 α] [分配乘法作用 M α] : 分配乘法作用 M (Shrink.{v} α)
  定义体: (equivShrink α).symm.distribMulAction M

Depends on / 依赖: distribMulAction, equivShrink, symm.distribMulAction
-/
instance [Monoid M] [AddCommMonoid α] [DistribMulAction M α] : DistribMulAction M (Shrink.{v} α) :=
  (equivShrink α).symm.distribMulAction M
