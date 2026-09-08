/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Submonoid.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set

/-!
# Submonoids in a group with zero
-/

@[expose] public section

assert_not_exists Ring

open Set
open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

namespace Submonoid
section GroupWithZero
variable [GroupWithZero G₀] [MulDistribMulAction G₀ M] {a : G₀}

@[simp]
/-
**Submonoid.smul_mem_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：smul_mem_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : a • x in a
 • S ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
lemma smul_mem_pointwise_smul_iff₀ (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set M) x
/-
**Submonoid.mem_pointwise_smul_iff_inv_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submo
noid`。
形式化陈述：mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Submonoid M} {x : M} : x 
in a • S ↔ a⁻¹ • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
-/
lemma mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set M) x
/-
**Submonoid.mem_inv_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_inv_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : x in a⁻¹ • 
S ↔ a • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
-/
lemma mem_inv_pointwise_smul_iff₀ (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set M) x

@[simp]
/-
**Submonoid.pointwise_smul_le_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subm
onoid`。
形式化陈述：pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Submonoid M} : a • S <
= a • T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_smul_set_iff`：smul_set_subset_smul_set_iff : a • A s
ubseteq a • B ↔ A subseteq B
-/
lemma pointwise_smul_le_pointwise_smul_iff₀ (ha : a ≠ 0) {S T : Submonoid M} :
    a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff₀ ha
/-
**Submonoid.pointwise_smul_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pointwise_smul_le_iff₀ (ha : a ≠ 0) {S T : Submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  smul_set_subset_iff₀ ha
/-
**Submonoid.le_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_pointwise_smul_iff₀ (ha : a ≠ 0) {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_smul_set_iff₀ ha

end GroupWithZero
end Submonoid

namespace AddSubmonoid
section Monoid
variable [DistribMulAction M A]

/-- The action on an additive submonoid corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/-
**AddSubmonoid.pointwiseMulAction** 是 Mathlib 中的一个定义，位于命名空间 `AddSubmonoid`。
形式化陈述：{M : Type u_3} →   {A : Type u_4} → [inst : Monoid M] → [inst_1 : AddMonoi
d A] → [DistribMulAction M A] → MulAction M (AddSubmonoid A)
参数：AddSubmonoid A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on an additive submonoid corresponding to applying the action to ever
y element.

This is available as an instance in the `Pointwise` locale.
-/
protected def pointwiseMulAction : MulAction M (AddSubmonoid A) where
  smul a S := S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_one _)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f : AddMonoid.End A => S.map f) (map_mul _ _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] AddSubmonoid.pointwiseMulAction

@[simp, norm_cast]
/-
**AddSubmonoid.coe_pointwise_smul** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmonoid`。
形式化陈述：coe_pointwise_smul (m : M) (S : AddSubmonoid A) : ↑(m • S) = m • (S : Set 
A)
参数：m : M；S : AddSubmonoid A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_pointwise_smul (m : M) (S : AddSubmonoid A) : ↑(m • S) = m • (S : Set A) := rfl
/-
**AddSubmonoid.smul_mem_pointwise_smul** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmonoid`。
形式化陈述：smul_mem_pointwise_smul (a : A) (m : M) (S : AddSubmonoid A) : a in S -> m
 • a in m • S
参数：a : A；m : M；S : AddSubmonoid A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
lemma smul_mem_pointwise_smul (a : A) (m : M) (S : AddSubmonoid A) : a ∈ S → m • a ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set A))
/-
**AddSubmonoid.mem_smul_pointwise_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmo
noid`。
形式化陈述：mem_smul_pointwise_iff_exists (a : A) (m : M) (S : AddSubmonoid A) : a in 
m • S ↔ exists s : A, s in S ∧ m • s = a
参数：a : A；m : M；S : AddSubmonoid A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
-/
lemma mem_smul_pointwise_iff_exists (a : A) (m : M) (S : AddSubmonoid A) :
    a ∈ m • S ↔ ∃ s : A, s ∈ S ∧ m • s = a :=
  (Set.mem_smul_set : a ∈ m • (S : Set A) ↔ _)

@[simp]
/-
**AddSubmonoid.smul_bot** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmonoid`。
形式化陈述：smul_bot (m : M) : m • (⊥ : AddSubmonoid A) = ⊥
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.map_bot`：∀ {M : Type u_1} {N : Type u_2} [inst : AddZeroCla
ss M] [inst_1 : AddZeroClass N] {F : Type u_4}   [inst_2 : FunLike F M N] [mc : 
AddMonoidH…
-/
lemma smul_bot (m : M) : m • (⊥ : AddSubmonoid A) = ⊥ := map_bot _
/-
**AddSubmonoid.smul_sup** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmonoid`。
形式化陈述：smul_sup (m : M) (S T : AddSubmonoid A) : m • (S ⊔ T) = m • S ⊔ m • T
参数：m : M；S T : AddSubmonoid A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.map_sup`：∀ {M : Type u_1} {N : Type u_2} [inst : AddZeroCla
ss M] [inst_1 : AddZeroClass N] {F : Type u_4}   [inst_2 : FunLike F M N] [mc : 
AddMonoidH…
-/
lemma smul_sup (m : M) (S T : AddSubmonoid A) : m • (S ⊔ T) = m • S ⊔ m • T :=
  map_sup _ _ _

@[simp]
/-
**AddSubmonoid.smul_closure** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmonoid`。
形式化陈述：smul_closure (m : M) (s : Set A) : m • closure s = closure (m • s)
参数：m : M；s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_mclosure`：∀ {M : Type u_1} {N : Type u_2} [inst : AddZe
roClass M] [inst_1 : AddZeroClass N] {F : Type u_4}   [inst_2 : FunLike F M N] [
mc : AddMonoidH…
-/
lemma smul_closure (m : M) (s : Set A) : m • closure s = closure (m • s) :=
  AddMonoidHom.map_mclosure _ _
/-
**AddSubmonoid.pointwise_isCentralScalar** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmonoid
`。
形式化陈述：pointwise_isCentralScalar [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A] 
: IsCentralScalar M (AddSubmonoid A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AddMonoid.End.instAddMonoidHomClass`：∀ (M : Type u_4) [inst : AddZero M]
, AddMonoidHomClass (AddMonoid.End M) M M
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
lemma pointwise_isCentralScalar [DistribMulAction Mᵐᵒᵖ A] [IsCentralScalar M A] :
    IsCentralScalar M (AddSubmonoid A) :=
  ⟨fun _ S =>
    (congr_arg fun f : AddMonoid.End A => S.map f) <| AddMonoidHom.ext <| op_smul_eq_smul _⟩

scoped[Pointwise] attribute [instance] AddSubmonoid.pointwise_isCentralScalar

end Monoid

section Group
variable [Group G] [DistribMulAction G A] {a : G}

@[simp]
/-
**AddSubmonoid.smul_mem_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmono
id`。
形式化陈述：smul_mem_pointwise_smul_iff {S : AddSubmonoid A} {x : A} : a • x in a • S 
↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
lemma smul_mem_pointwise_smul_iff {S : AddSubmonoid A} {x : A} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff
/-
**AddSubmonoid.mem_pointwise_smul_iff_inv_smul_mem** 是 Mathlib 中的一个引理，位于命名空间 `Ad
dSubmonoid`。
形式化陈述：mem_pointwise_smul_iff_inv_smul_mem {S : AddSubmonoid A} {x : A} : x in a 
• S ↔ a⁻¹ • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
-/
lemma mem_pointwise_smul_iff_inv_smul_mem {S : AddSubmonoid A} {x : A} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem
/-
**AddSubmonoid.mem_inv_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmonoi
d`。
形式化陈述：mem_inv_pointwise_smul_iff {S : AddSubmonoid A} {x : A} : x in a⁻¹ • S ↔ a
 • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
-/
lemma mem_inv_pointwise_smul_iff {S : AddSubmonoid A} {x : A} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
/-
**AddSubmonoid.pointwise_smul_le_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `A
ddSubmonoid`。
形式化陈述：pointwise_smul_le_pointwise_smul_iff {S T : AddSubmonoid A} : a • S <= a •
 T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_smul_set_iff`：smul_set_subset_smul_set_iff : a • A s
ubseteq a • B ↔ A subseteq B
-/
lemma pointwise_smul_le_pointwise_smul_iff {S T : AddSubmonoid A} :
    a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff
/-
**AddSubmonoid.pointwise_smul_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmonoid`。
形式化陈述：pointwise_smul_le_iff {S T : AddSubmonoid A} : a • S <= T ↔ S <= a⁻¹ • T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_iff_subset_inv_smul_set`：smul_set_subset_iff_subset_
inv_smul_set : a • A subseteq B ↔ A subseteq a⁻¹ • B
-/
lemma pointwise_smul_le_iff {S T : AddSubmonoid A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  smul_set_subset_iff_subset_inv_smul_set
/-
**AddSubmonoid.le_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmonoid`。
形式化陈述：le_pointwise_smul_iff {S T : AddSubmonoid A} : S <= a • T ↔ a⁻¹ • S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
-/
lemma le_pointwise_smul_iff {S T : AddSubmonoid A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_smul_set_iff

end Group

section GroupWithZero
variable [GroupWithZero G₀] [DistribMulAction G₀ A] {S T : AddSubmonoid A} {a : G₀}

@[simp]
/-
**AddSubmonoid.smul_mem_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmono
id`。
形式化陈述：smul_mem_pointwise_smul_iff {S : AddSubmonoid A} {x : A} : a • x in a • S 
↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
lemma smul_mem_pointwise_smul_iff₀ (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set A) x
/-
**AddSubmonoid.mem_pointwise_smul_iff_inv_smul_mem** 是 Mathlib 中的一个引理，位于命名空间 `Ad
dSubmonoid`。
形式化陈述：mem_pointwise_smul_iff_inv_smul_mem {S : AddSubmonoid A} {x : A} : x in a 
• S ↔ a⁻¹ • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
-/
lemma mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x
/-
**AddSubmonoid.mem_inv_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmonoi
d`。
形式化陈述：mem_inv_pointwise_smul_iff {S : AddSubmonoid A} {x : A} : x in a⁻¹ • S ↔ a
 • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
-/
lemma mem_inv_pointwise_smul_iff₀ (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set A) x

@[simp]
/-
**AddSubmonoid.pointwise_smul_le_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `A
ddSubmonoid`。
形式化陈述：pointwise_smul_le_pointwise_smul_iff {S T : AddSubmonoid A} : a • S <= a •
 T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_smul_set_iff`：smul_set_subset_smul_set_iff : a • A s
ubseteq a • B ↔ A subseteq B
-/
lemma pointwise_smul_le_pointwise_smul_iff₀ (ha : a ≠ 0) : a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff₀ ha
/-
**AddSubmonoid.pointwise_smul_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmonoid`。
形式化陈述：pointwise_smul_le_iff {S T : AddSubmonoid A} : a • S <= T ↔ S <= a⁻¹ • T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_iff_subset_inv_smul_set`：smul_set_subset_iff_subset_
inv_smul_set : a • A subseteq B ↔ A subseteq a⁻¹ • B
-/
lemma pointwise_smul_le_iff₀ (ha : a ≠ 0) : a • S ≤ T ↔ S ≤ a⁻¹ • T := smul_set_subset_iff₀ ha
/-
**AddSubmonoid.le_pointwise_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `AddSubmonoid`。
形式化陈述：le_pointwise_smul_iff {S T : AddSubmonoid A} : S <= a • T ↔ a⁻¹ • S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
-/
lemma le_pointwise_smul_iff₀ (ha : a ≠ 0) : S ≤ a • T ↔ a⁻¹ • S ≤ T := subset_smul_set_iff₀ ha

end GroupWithZero
end AddSubmonoid

