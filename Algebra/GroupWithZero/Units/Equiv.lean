/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Multiplication by a nonzero element in a `GroupWithZero` is a permutation.
-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

variable {G₀ : Type*}

namespace Equiv
section GroupWithZero
variable [GroupWithZero G₀]

/-- In a `GroupWithZero` `G₀`, the unit group `G₀ˣ` is equivalent to the subtype of nonzero
elements. -/
/-
**Equiv._root_.unitsEquivNeZero** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a `GroupWithZero` `G₀`, the unit group `G₀ˣ` is equivalent to the subtype of 
nonzero
elements.
-/
@[simps] def _root_.unitsEquivNeZero : G₀ˣ ≃ {a : G₀ // a ≠ 0} where
  toFun a := ⟨a, a.ne_zero⟩
  invFun a := Units.mk0 _ a.prop

/-- Left multiplication by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! -fullyApplied]
/-
**Equiv.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{G : Type u_5} → [Group G] → G → Equiv.Perm G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left multiplication by a nonzero element in a `GroupWithZero` is a permutation o
f the
underlying type.
-/
protected def mulLeft₀ (a : G₀) (ha : a ≠ 0) : Perm G₀ :=
  (Units.mk0 a ha).mulLeft
/-
**Equiv._root_.mulLeft_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.mulLeft_bijective₀ (a : G₀) (ha : a ≠ 0) : Function.Bijective (a * · : G₀ → G₀) :=
  (Equiv.mulLeft₀ a ha).bijective

/-- Right multiplication by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! -fullyApplied]
/-
**Equiv.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{G : Type u_5} → [Group G] → G → Equiv.Perm G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right multiplication by a nonzero element in a `GroupWithZero` is a permutation 
of the
underlying type.
-/
protected def mulRight₀ (a : G₀) (ha : a ≠ 0) : Perm G₀ :=
  (Units.mk0 a ha).mulRight
/-
**Equiv._root_.mulRight_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.mulRight_bijective₀ (a : G₀) (ha : a ≠ 0) : Function.Bijective ((· * a) : G₀ → G₀) :=
  (Equiv.mulRight₀ a ha).bijective

/-- Right division by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! +simpRhs]
/-
**Equiv.divRight** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{G : Type u_5} → [Group G] → G → G ≃ G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right division by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type.
-/
def divRight₀ (a : G₀) (ha : a ≠ 0) : Perm G₀ where
  toFun := (· / a)
  invFun := (· * a)
  left_inv _ := by simp [ha]
  right_inv _ := by simp [ha]

end GroupWithZero

section CommGroupWithZero
variable [CommGroupWithZero G₀]

/-- Left division by a nonzero element in a `CommGroupWithZero` is a permutation of the underlying
type. -/
@[simps! +simpRhs]
/-
**Equiv.divLeft** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{G : Type u_5} → [Group G] → G → G ≃ G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left division by a nonzero element in a `CommGroupWithZero` is a permutation of 
the underlying
type.
-/
def divLeft₀ (a : G₀) (ha : a ≠ 0) : Perm G₀ where
  toFun := (a / ·)
  invFun := (a / ·)
  left_inv _ := by simp [ha]
  right_inv _ := by simp [ha]

end CommGroupWithZero
end Equiv

