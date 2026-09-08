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

/-
**PUnit.commRing** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：commRing : CommRing PUnit where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.add_comm`：∀ {G : Type u} [self : AddCommGroup G] (a b : G),
 a + b = b + a
· 使用定理 `CommGroup.mul_comm`：∀ {G : Type u} [self : CommGroup G] (a b : G), a * b
 = b * a
-/
instance commRing : CommRing PUnit where
  __ := PUnit.commGroup
  __ := PUnit.addCommGroup
  left_distrib := by intros; rfl
  right_distrib := by intros; rfl
  zero_mul := by intros; rfl
  mul_zero := by intros; rfl
  natCast _ := unit
/-
**PUnit.** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCancelMulZero PUnit where
  mul_left_cancel_of_ne_zero := by simp
  mul_right_cancel_of_ne_zero := by simp

end PUnit

