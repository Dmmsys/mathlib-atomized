/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Instances on pempty

This file collects facts about algebraic structures on the (universe-polymorphic) empty type, e.g.
that it is a semigroup.
-/

public section


universe u

@[to_additive]
/--
Instance `SemigroupPEmpty` / 实例 `SemigroupPEmpty`

English:
instance SemigroupPEmpty
  signature: : Semigroup PEmpty.{u + 1} where
  body: by cases x
  mul_assoc x y z := by cases x

中文:
实例 SemigroupPEmpty
  签名: : Semigroup PEmpty.{u + 1} where
  定义体: by cases x
  mul_assoc x y z := by cases x

Depends on / 依赖: mul_assoc
-/
instance SemigroupPEmpty : Semigroup PEmpty.{u + 1} where
  mul x _ := by cases x
  mul_assoc x y z := by cases x
