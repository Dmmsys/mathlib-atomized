/-
Copyright (c) 2024 David Ang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ang
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# The subgroup of fixed points of an action
-/

@[expose] public section

variable (M α : Type*) [Monoid M]

section AddMonoid
variable [AddMonoid α] [DistribMulAction M α]

/-- The additive submonoid of elements fixed under the whole action. -/
/-
**FixedPoints.addSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FixedPoints.addSubmonoid : AddSubmonoid α where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive submonoid of elements fixed under the whole action.
-/
def FixedPoints.addSubmonoid : AddSubmonoid α where
  carrier := MulAction.fixedPoints M α
  zero_mem' := smul_zero
  add_mem' ha hb _ := by rw [smul_add, ha, hb]

@[simp]
/-
**FixedPoints.mem_addSubmonoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FixedPoints.mem_addSubmonoid (a : α) : a in addSubmonoid M α ↔ forall m : 
M, m • a = a
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma FixedPoints.mem_addSubmonoid (a : α) : a ∈ addSubmonoid M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl

end AddMonoid

section AddGroup
variable [AddGroup α] [DistribMulAction M α]

/-- The additive subgroup of elements fixed under the whole action. -/
/-
**FixedPoints.addSubgroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FixedPoints.addSubgroup : AddSubgroup α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive subgroup of elements fixed under the whole action.
-/
def FixedPoints.addSubgroup : AddSubgroup α where
  __ := addSubmonoid M α
  neg_mem' ha _ := by rw [smul_neg, ha]

@[simp]
/-
**FixedPoints.mem_addSubgroup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FixedPoints.mem_addSubgroup (a : α) : a in FixedPoints.addSubgroup M α ↔ f
orall m : M, m • a = a
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma FixedPoints.mem_addSubgroup (a : α) : a ∈ FixedPoints.addSubgroup M α ↔ ∀ m : M, m • a = a :=
  Iff.rfl

@[simp]
/-
**FixedPoints.addSubgroup_toAddSubmonoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FixedPoints.addSubgroup_toAddSubmonoid : (FixedPoints.addSubgroup M α).toA
ddSubmonoid = addSubmonoid M α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FixedPoints.addSubgroup_toAddSubmonoid :
    (FixedPoints.addSubgroup M α).toAddSubmonoid = addSubmonoid M α :=
  rfl

end AddGroup

