/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.GroupWithZero.Submonoid.Pointwise

/-!
# Subgroups in a group with zero
-/

@[expose] public section

assert_not_exists Ring

open Set
open scoped Pointwise

variable {G₀ G M A : Type*}

namespace Subgroup
section GroupWithZero
variable [GroupWithZero G₀] [Group G] [MulDistribMulAction G₀ G] {S T : Subgroup G} {a : G₀}

@[simp]
/-
**Subgroup.smul_mem_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：smul_mem_pointwise_smul_iff {a : α} {S : Subgroup G} {x : G} : a • x in a 
• S ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
lemma smul_mem_pointwise_smul_iff₀ (ha : a ≠ 0) (S : Subgroup G) (x : G) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set G) x
/-
**Subgroup.mem_pointwise_smul_iff_inv_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up`。
形式化陈述：mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Subgroup G} {x : G} : x i
n a • S ↔ a⁻¹ • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
-/
lemma mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a ≠ 0) (S : Subgroup G) (x : G) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set G) x
/-
**Subgroup.mem_inv_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_inv_pointwise_smul_iff {a : α} {S : Subgroup G} {x : G} : x in a⁻¹ • S
 ↔ a • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
-/
lemma mem_inv_pointwise_smul_iff₀ (ha : a ≠ 0) (S : Subgroup G) (x : G) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set G) x

@[simp]
/-
**Subgroup.pointwise_smul_le_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgr
oup`。
形式化陈述：pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Subgroup G} : a • S <=
 a • T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_smul_set_iff`：smul_set_subset_smul_set_iff : a • A s
ubseteq a • B ↔ A subseteq B
-/
lemma pointwise_smul_le_pointwise_smul_iff₀ (ha : a ≠ 0) : a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff₀ ha
/-
**Subgroup.pointwise_smul_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pointwise_smul_le_iff₀ (ha : a ≠ 0) : a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff₀ ha
/-
**Subgroup.le_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_pointwise_smul_iff₀ (ha : a ≠ 0) : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff₀ ha

end GroupWithZero
end Subgroup

namespace AddSubgroup
section Monoid
variable [Monoid M] [AddGroup A] [DistribMulAction M A] {a : M}

/-- The action on an additive subgroup corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/-
**AddSubgroup.pointwiseMulAction** 是 Mathlib 中的一个定义，位于命名空间 `AddSubgroup`。
形式化陈述：{M : Type u_3} →   {A : Type u_4} → [inst : Monoid M] → [inst_1 : AddGroup
 A] → [DistribMulAction M A] → MulAction M (AddSubgroup A)
参数：AddSubgroup A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on an additive subgroup corresponding to applying the action to every
 element.

This is available as an instance in the `Pointwise` locale.
-/
protected def pointwiseMulAction : MulAction M (AddSubgroup A) where
  smul a S := S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_one _)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_mul _ _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] AddSubgroup.pointwiseMulAction
/-
**AddSubgroup.pointwise_smul_def** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：pointwise_smul_def (S : AddSubgroup A) : a • S = S.map (DistribMulAction.t
oAddMonoidEnd _ _ a)
参数：S : AddSubgroup A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pointwise_smul_def (S : AddSubgroup A) :
    a • S = S.map (DistribMulAction.toAddMonoidEnd _ _ a) :=
  rfl

@[simp, norm_cast]
/-
**AddSubgroup.coe_pointwise_smul** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：coe_pointwise_smul (a : M) (S : AddSubgroup A) : ↑(a • S) = a • (S : Set A
)
参数：a : M；S : AddSubgroup A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_pointwise_smul (a : M) (S : AddSubgroup A) : ↑(a • S) = a • (S : Set A) :=
  rfl

@[simp]
/-
**AddSubgroup.pointwise_smul_toAddSubmonoid** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgro
up`。
形式化陈述：pointwise_smul_toAddSubmonoid (a : M) (S : AddSubgroup A) : (a • S).toAddS
ubmonoid = a • S.toAddSubmonoid
参数：a : M；S : AddSubgroup A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pointwise_smul_toAddSubmonoid (a : M) (S : AddSubgroup A) :
    (a • S).toAddSubmonoid = a • S.toAddSubmonoid :=
  rfl
/-
**AddSubgroup.smul_mem_pointwise_smul** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：smul_mem_pointwise_smul (m : A) (a : M) (S : AddSubgroup A) : m in S -> a 
• m in a • S
参数：m : A；a : M；S : AddSubgroup A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
lemma smul_mem_pointwise_smul (m : A) (a : M) (S : AddSubgroup A) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set A))
/-
**AddSubgroup.mem_smul_pointwise_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgro
up`。
形式化陈述：mem_smul_pointwise_iff_exists (m : A) (a : M) (S : AddSubgroup A) : m in a
 • S ↔ exists s : A, s in S ∧ a • s = m
参数：m : A；a : M；S : AddSubgroup A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
-/
lemma mem_smul_pointwise_iff_exists (m : A) (a : M) (S : AddSubgroup A) :
    m ∈ a • S ↔ ∃ s : A, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set A) ↔ _)
/-
**AddSubgroup.pointwise_isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `AddSubgroup`。
形式化陈述：pointwise_isCentralScalar [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A] 
: IsCentralScalar M (AddSubgroup A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance pointwise_isCentralScalar [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A] :
    IsCentralScalar M (AddSubgroup A) :=
  ⟨fun _ S => (congr_arg fun f => S.map f) <| AddMonoidHom.ext <| op_smul_eq_smul _⟩

-- TODO: Check that these lemmas are useful and uncomment.
-- @[simp]
-- lemma smul_bot (m : M) : m • (⊥ : AddSubgroup A) = ⊥ := map_bot _

-- lemma smul_sup (m : M) (S T : AddSubgroup A) : m • (S ⊔ T) = m • S ⊔ m • T := map_sup _ _ _

-- @[simp]
-- lemma smul_closure (m : M) (s : Set A) : m • closure s = closure (m • s) :=
--   AddMonoidHom.map_closure ..

scoped[Pointwise] attribute [instance] AddSubgroup.pointwise_isCentralScalar

end Monoid

section Group
variable [Group G] [AddGroup A] [DistribMulAction G A] {S T : AddSubgroup A} {a : G} {x : A}

/-
**AddSubgroup.smul_mem_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgroup
`。
形式化陈述：∀ {G : Type u_2} {A : Type u_4} [inst : Group G] [inst_1 : AddGroup A] [in
st_2 : DistribMulAction G A]   {S : AddSubgroup A} {a : G} {x : A}, a • x ∈ a • 
S ↔ x ∈ S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
@[simp] lemma smul_mem_pointwise_smul_iff : a • x ∈ a • S ↔ x ∈ S := smul_mem_smul_set_iff
/-
**AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem** 是 Mathlib 中的一个引理，位于命名空间 `Add
Subgroup`。
形式化陈述：mem_pointwise_smul_iff_inv_smul_mem : x in a • S ↔ a⁻¹ • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
-/
lemma mem_pointwise_smul_iff_inv_smul_mem : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem
/-
**AddSubgroup.mem_inv_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`
。
形式化陈述：mem_inv_pointwise_smul_iff : x in a⁻¹ • S ↔ a • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
-/
lemma mem_inv_pointwise_smul_iff : x ∈ a⁻¹ • S ↔ a • x ∈ S := mem_inv_smul_set_iff

@[simp]
/-
**AddSubgroup.pointwise_smul_le_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ad
dSubgroup`。
形式化陈述：pointwise_smul_le_pointwise_smul_iff : a • S <= a • T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_smul_set_iff`：smul_set_subset_smul_set_iff : a • A s
ubseteq a • B ↔ A subseteq B
-/
lemma pointwise_smul_le_pointwise_smul_iff : a • S ≤ a • T ↔ S ≤ T := smul_set_subset_smul_set_iff
/-
**AddSubgroup.pointwise_smul_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：pointwise_smul_le_iff : a • S <= T ↔ S <= a⁻¹ • T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_iff_subset_inv_smul_set`：smul_set_subset_iff_subset_
inv_smul_set : a • A subseteq B ↔ A subseteq a⁻¹ • B
-/
lemma pointwise_smul_le_iff : a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff_subset_inv_smul_set
/-
**AddSubgroup.le_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：le_pointwise_smul_iff : S <= a • T ↔ a⁻¹ • S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
-/
lemma le_pointwise_smul_iff : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff

end Group

section GroupWithZero
variable [GroupWithZero G₀] [AddGroup A] [DistribMulAction G₀ A] {S T : AddSubgroup A} {a : G₀}

@[simp]
/-
**AddSubgroup.smul_mem_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddSubgroup
`。
形式化陈述：∀ {G : Type u_2} {A : Type u_4} [inst : Group G] [inst_1 : AddGroup A] [in
st_2 : DistribMulAction G A]   {S : AddSubgroup A} {a : G} {x : A}, a • x ∈ a • 
S ↔ x ∈ S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
lemma smul_mem_pointwise_smul_iff₀ (ha : a ≠ 0) (S : AddSubgroup A) (x : A) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set A) x
/-
**AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem** 是 Mathlib 中的一个引理，位于命名空间 `Add
Subgroup`。
形式化陈述：mem_pointwise_smul_iff_inv_smul_mem : x in a • S ↔ a⁻¹ • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
-/
lemma mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a ≠ 0) (S : AddSubgroup A) (x : A) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x
/-
**AddSubgroup.mem_inv_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`
。
形式化陈述：mem_inv_pointwise_smul_iff : x in a⁻¹ • S ↔ a • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
-/
lemma mem_inv_pointwise_smul_iff₀ (ha : a ≠ 0) (S : AddSubgroup A) (x : A) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set A) x

@[simp]
/-
**AddSubgroup.pointwise_smul_le_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ad
dSubgroup`。
形式化陈述：pointwise_smul_le_pointwise_smul_iff : a • S <= a • T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_smul_set_iff`：smul_set_subset_smul_set_iff : a • A s
ubseteq a • B ↔ A subseteq B
-/
lemma pointwise_smul_le_pointwise_smul_iff₀ (ha : a ≠ 0) : a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff₀ ha
/-
**AddSubgroup.pointwise_smul_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：pointwise_smul_le_iff : a • S <= T ↔ S <= a⁻¹ • T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_iff_subset_inv_smul_set`：smul_set_subset_iff_subset_
inv_smul_set : a • A subseteq B ↔ A subseteq a⁻¹ • B
-/
lemma pointwise_smul_le_iff₀ (ha : a ≠ 0) : a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff₀ ha
/-
**AddSubgroup.le_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：le_pointwise_smul_iff : S <= a • T ↔ a⁻¹ • S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
-/
lemma le_pointwise_smul_iff₀ (ha : a ≠ 0) : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff₀ ha

end GroupWithZero
end AddSubgroup

