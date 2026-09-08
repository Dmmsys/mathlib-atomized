/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.GroupTheory.Finiteness

/-!
# Affine monoids

This file defines affine monoids as finitely generated cancellative torsion-free commutative
monoids.
-/

public section

/-- An affine monoid is a finitely generated cancellative torsion-free commutative monoid. -/
/-
**abbrev** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：abbrev IsAffineAddMonoid (M : Type*) [AddCommMonoid M] : Prop
参数：M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine monoid is a finitely generated cancellative torsion-free commutative m
onoid.
-/
class abbrev IsAffineAddMonoid (M : Type*) [AddCommMonoid M] : Prop :=
  IsCancelAdd M, AddMonoid.FG M, IsAddTorsionFree M

/-- An affine monoid is a finitely generated cancellative torsion-free commutative monoid. -/
@[to_additive]
/-
**abbrev** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：abbrev IsAffineAddMonoid (M : Type*) [AddCommMonoid M] : Prop
参数：M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine monoid is a finitely generated cancellative torsion-free commutative m
onoid.
-/
class abbrev IsAffineMonoid (M : Type*) [CommMonoid M] : Prop :=
  IsCancelMul M, Monoid.FG M, IsMulTorsionFree M
