/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Distributive actions by submonoids
-/

public section

assert_not_exists RelIso Ring

namespace Submonoid

variable {M α : Type*} [Monoid M]

variable {S : Type*} [SetLike S M] (s : S) [SubmonoidClass S M]

/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [AddMonoid α] [DistribMulAction M α] : DistribMulAction s α where
  smul_zero r := smul_zero (r : M)
  smul_add r := smul_add (r : M)

/-- The action by a submonoid is the action by the underlying monoid. -/
/-
**Submonoid.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：distribMulAction [AddMonoid α] [DistribMulAction M α] (S : Submonoid M) : 
DistribMulAction S α
参数：S : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a submonoid is the action by the underlying monoid.
-/
instance distribMulAction [AddMonoid α] [DistribMulAction M α] (S : Submonoid M) :
    DistribMulAction S α :=
  inferInstance
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [Monoid α] [MulDistribMulAction M α] : MulDistribMulAction s α where
  smul_mul r := smul_mul' (r : M)
  smul_one r := smul_one (r : M)

/-- The action by a submonoid is the action by the underlying monoid. -/
/-
**Submonoid.mulDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：mulDistribMulAction [Monoid α] [MulDistribMulAction M α] (S : Submonoid M)
 : MulDistribMulAction S α
参数：S : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a submonoid is the action by the underlying monoid.
-/
instance mulDistribMulAction [Monoid α] [MulDistribMulAction M α] (S : Submonoid M) :
    MulDistribMulAction S α :=
  inferInstance

end Submonoid

