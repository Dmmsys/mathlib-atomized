/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.DistribMulAction
public import Mathlib.Algebra.Ring.Action.Basic

/-!
# Instances of `MulSemiringAction` for subobjects

These are defined in this file as `Semiring`s are not available yet where `Submonoid` and `Subgroup`
are defined.

Instances for `Subsemiring` and `Subring` are provided next to the other scalar actions instances
for those subobjects.

-/

public section

assert_not_exists RelIso

variable {M G R : Type*}
variable [Monoid M] [Group G] [Semiring R]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [MulSemiringAction M R] {S : Type*} [SetLike S M] (s : S)
    [SubmonoidClass S M] : MulSemiringAction s R :=
  { (inferInstance : DistribMulAction s R), (inferInstance : MulDistribMulAction s R) with }

/-- A stronger version of `Submonoid.distribMulAction`. -/
/-
**Submonoid.mulSemiringAction** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submonoid.mulSemiringAction [MulSemiringAction M R] (H : Submonoid M) : Mu
lSemiringAction H R
参数：H : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A stronger version of `Submonoid.distribMulAction`.
-/
instance Submonoid.mulSemiringAction [MulSemiringAction M R] (H : Submonoid M) :
    MulSemiringAction H R :=
  inferInstance

/-- A stronger version of `Subgroup.distribMulAction`. -/
/-
**Subgroup.mulSemiringAction** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subgroup.mulSemiringAction [MulSemiringAction G R] (H : Subgroup G) : MulS
emiringAction H R
参数：H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A stronger version of `Subgroup.distribMulAction`.
-/
instance Subgroup.mulSemiringAction [MulSemiringAction G R] (H : Subgroup G) :
    MulSemiringAction H R :=
  inferInstance
