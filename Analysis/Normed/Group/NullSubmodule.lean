/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.MulAction

/-!
# The null subgroup in a seminormed commutative group

For any `SeminormedAddCommGroup M`, the quotient `SeparationQuotient M` by the null subgroup is
defined as a `NormedAddCommGroup` instance in `Mathlib/Analysis/Normed/Group/Uniform.lean`. Here we
define the null space as a subgroup.

## Main definitions

We use `M` to denote seminormed groups.

* `nullAddSubgroup` : the subgroup of elements `x` with `‖x‖ = 0`.

If `E` is a vector space over `𝕜` with an appropriate continuous action, we also define the null
subspace as a submodule of `E`.

* `nullSubmodule` : the subspace of elements `x` with `‖x‖ = 0`.

-/

@[expose] public section

variable {M : Type*} [SeminormedCommGroup M]

variable (M) in
/-- The null subgroup with respect to the norm. -/
@[to_additive /-- The additive null subgroup with respect to the norm. -/]
/-
**nullSubgroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nullSubgroup : Subgroup M where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The null subgroup with respect to the norm.
-/
def nullSubgroup : Subgroup M where
  carrier := {x : M | ‖x‖ = 0}
  mul_mem' {x y} (hx : ‖x‖ = 0) (hy : ‖y‖ = 0) := by
    apply le_antisymm _ (norm_nonneg' _)
    refine (norm_mul_le' x y).trans_eq ?_
    rw [hx, hy, add_zero]
  one_mem' := norm_one'
  inv_mem' {x} (hx : ‖x‖ = 0) := by simpa only [Set.mem_ofPred_eq, norm_inv'] using hx

@[to_additive]
/-
**isClosed_nullSubgroup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_nullSubgroup : IsClosed (nullSubgroup M : Set M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_norm'`：continuous_norm' : Continuous fun a : E => ‖a‖
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
lemma isClosed_nullSubgroup : IsClosed (nullSubgroup M : Set M) := by
  apply isClosed_singleton.preimage continuous_norm'

@[to_additive (attr := simp)]
/-
**mem_nullSubgroup_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_nullSubgroup_iff {x : M} : x in nullSubgroup M ↔ ‖x‖ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_nullSubgroup_iff {x : M} : x ∈ nullSubgroup M ↔ ‖x‖ = 0 := Iff.rfl

variable {𝕜 E : Type*}
variable [SeminormedAddCommGroup E] [SeminormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

variable (𝕜 E) in
/-- The null space with respect to the norm. -/
/-
**nullSubmodule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：nullSubmodule : Submodule 𝕜 E where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The null space with respect to the norm.
-/
def nullSubmodule : Submodule 𝕜 E where
  __ := nullAddSubgroup E
  smul_mem' c x (hx : ‖x‖ = 0) := by
    apply le_antisymm _ (norm_nonneg _)
    refine (norm_smul_le _ _).trans_eq ?_
    rw [hx, mul_zero]
/-
**isClosed_nullSubmodule** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_nullSubmodule : IsClosed (nullSubmodule 𝕜 E : Set E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_nullAddSubgroup`：∀ {M : Type u_1} [inst : SeminormedAddCommGrou
p M], IsClosed ↑(nullAddSubgroup M)
-/
lemma isClosed_nullSubmodule : IsClosed (nullSubmodule 𝕜 E : Set E) := isClosed_nullAddSubgroup

@[simp]
/-
**mem_nullSubmodule_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_nullSubmodule_iff {x : E} : x in nullSubmodule 𝕜 E ↔ ‖x‖ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_nullSubmodule_iff {x : E} : x ∈ nullSubmodule 𝕜 E ↔ ‖x‖ = 0 := Iff.rfl
