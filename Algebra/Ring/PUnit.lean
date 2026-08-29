/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Ring.Defs

/-!
# `PUnit` is a commutative ring

This file collects facts about algebraic structures on the one-element type, e.g. that it is a
commutative ring.
-/

public section

assert_not_exists Field

namespace PUnit

/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: : CommRing PUnit where
  body: PUnit.commGroup
  __ := PUnit.addCommGroup
  left_distrib := by intros; rfl
  right_distrib := by intros; rfl
  zero_mul := by intros; rfl
  mul_zero := by intros; rfl
  natCast _ := unit

中文:
实例 commRing
  签名: : 交换环 命题单元 where
  定义体: PUnit.commGroup
  __ := PUnit.addCommGroup
  left_distrib := by intros; rfl
  right_distrib := by intros; rfl
  zero_mul := by intros; rfl
  mul_zero := by intros; rfl
  natCast _ := unit

Depends on / 依赖: PUnit.commGroup, commGroup
-/
instance commRing : CommRing PUnit where
  __ := PUnit.commGroup
  __ := PUnit.addCommGroup
  left_distrib := by intros; rfl
  right_distrib := by intros; rfl
  zero_mul := by intros; rfl
  mul_zero := by intros; rfl
  natCast _ := unit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCancelMulZero PUnit
  body: by simp
  mul_right_cancel_of_ne_zero := by simp

中文:
实例 :
  签名: 是乘零消去 命题单元
  定义体: by simp
  mul_right_cancel_of_ne_zero := by simp
-/
instance : IsCancelMulZero PUnit where
  mul_left_cancel_of_ne_zero := by simp
  mul_right_cancel_of_ne_zero := by simp

end PUnit
