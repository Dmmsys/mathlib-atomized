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

/--
Definition of `abbrev` / `abbrev` 的定义

English:
class abbrev
  parameters: IsAffineAddMonoid (M : Type*) [AddCommMonoid M]
  (no additional axioms)

中文:
类 abbrev
  参数: IsAffineAddMonoid (M : 类型) [AddCommMonoid M]
  (无附加公理)

Depends on / 依赖: AddMonoid, AddMonoid.FG, IsAddTorsionFree, IsCancelAdd
-/
class abbrev IsAffineAddMonoid (M : Type*) [AddCommMonoid M] : Prop :=
  IsCancelAdd M, AddMonoid.FG M, IsAddTorsionFree M

/-- An affine monoid is a finitely generated cancellative torsion-free commutative monoid. -/
@[to_additive]
/--
Definition of `abbrev` / `abbrev` 的定义

English:
class abbrev
  parameters: IsAffineMonoid (M : Type*) [CommMonoid M]
  (no additional axioms)

中文:
类 abbrev
  参数: IsAffineMonoid (M : 类型) [CommMonoid M]
  (无附加公理)
-/
class abbrev IsAffineMonoid (M : Type*) [CommMonoid M] : Prop :=
  IsCancelMul M, Monoid.FG M, IsMulTorsionFree M
