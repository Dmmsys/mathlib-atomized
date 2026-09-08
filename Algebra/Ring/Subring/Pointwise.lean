/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Pointwise

/-! # Pointwise instances on `Subring`s

This file provides the action `Subring.pointwiseMulAction` which matches the action of
`mulActionSet`.

This actions is available in the `Pointwise` locale.

## Implementation notes

This file is almost identical to the file `Mathlib/Algebra/Ring/Subsemiring/Pointwise.lean`. Where
possible, try to keep them in sync.

-/

@[expose] public section


open Set

variable {M R : Type*}

namespace Subring

section Monoid

variable [Monoid M] [Ring R] [MulSemiringAction M R]

/-- The action on a subring corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/-
**Subring.pointwiseMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：{M : Type u_1} →   {R : Type u_2} → [inst : Monoid M] → [inst_1 : Ring R] 
→ [MulSemiringAction M R] → MulAction M (Subring R)
参数：Subring R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on a subring corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.
-/
protected def pointwiseMulAction : MulAction M (Subring R) where
  smul a S := S.map (MulSemiringAction.toRingHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (RingHom.ext <| one_smul M)).trans S.map_id
  mul_smul _ _ S :=
    (congr_arg (fun f => S.map f) (RingHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Subring.pointwiseMulAction

open scoped Pointwise
/-
**Subring.pointwise_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：pointwise_smul_def {a : M} (S : Subring R) : a • S = S.map (MulSemiringAct
ion.toRingHom _ _ a)
参数：S : Subring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_def {a : M} (S : Subring R) :
    a • S = S.map (MulSemiringAction.toRingHom _ _ a) :=
  rfl

@[simp, norm_cast]
/-
**Subring.coe_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_pointwise_smul (m : M) (S : Subring R) : ↑(m • S) = m • (S : Set R)
参数：m : M；S : Subring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pointwise_smul (m : M) (S : Subring R) : ↑(m • S) = m • (S : Set R) :=
  rfl

@[simp]
/-
**Subring.pointwise_smul_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：pointwise_smul_toAddSubgroup (m : M) (S : Subring R) : (m • S).toAddSubgro
up = m • S.toAddSubgroup
参数：m : M；S : Subring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_toAddSubgroup (m : M) (S : Subring R) :
    (m • S).toAddSubgroup = m • S.toAddSubgroup :=
  rfl

@[simp]
/-
**Subring.pointwise_smul_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：pointwise_smul_toSubsemiring (m : M) (S : Subring R) : (m • S).toSubsemiri
ng = m • S.toSubsemiring
参数：m : M；S : Subring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_toSubsemiring (m : M) (S : Subring R) :
    (m • S).toSubsemiring = m • S.toSubsemiring :=
  rfl
/-
**Subring.smul_mem_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：smul_mem_pointwise_smul (m : M) (r : R) (S : Subring R) : r in S -> m • r 
in m • S
参数：m : M；r : R；S : Subring R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem smul_mem_pointwise_smul (m : M) (r : R) (S : Subring R) : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set R))
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CovariantClass M (Subring R) HSMul.hSMul LE.le :=
  ⟨fun _ _ => image_mono⟩
/-
**Subring.mem_smul_pointwise_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_smul_pointwise_iff_exists (m : M) (r : R) (S : Subring R) : r in m • S
 ↔ exists s : R, s in S ∧ m • s = r
参数：m : M；r : R；S : Subring R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
-/
theorem mem_smul_pointwise_iff_exists (m : M) (r : R) (S : Subring R) :
    r ∈ m • S ↔ ∃ s : R, s ∈ S ∧ m • s = r :=
  (Set.mem_smul_set : r ∈ m • (S : Set R) ↔ _)

@[simp]
/-
**Subring.smul_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：smul_bot (a : M) : a • (⊥ : Subring R) = ⊥
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.map_bot`：map_bot (f : R ->+* S) : (⊥ : Subring R).map f = ⊥
-/
theorem smul_bot (a : M) : a • (⊥ : Subring R) = ⊥ :=
  map_bot _
/-
**Subring.smul_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：smul_sup (a : M) (S T : Subring R) : a • (S ⊔ T) = a • S ⊔ a • T
参数：a : M；S T : Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.map_sup`：map_sup (s t : Subring R) (f : R ->+* S) : (s ⊔ t).map 
f = s.map f ⊔ t.map f
-/
theorem smul_sup (a : M) (S T : Subring R) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _
/-
**Subring.smul_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：smul_closure (a : M) (s : Set R) : a • closure s = closure (a • s)
参数：a : M；s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_closure`：map_closure (f : R ->+* S) (s : Set R) : (closure s
).map f = closure (f '' s)
-/
theorem smul_closure (a : M) (s : Set R) : a • closure s = closure (a • s) :=
  RingHom.map_closure _ _
/-
**Subring.pointwise_central_scalar** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
形式化陈述：pointwise_central_scalar [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R] 
: IsCentralScalar M (Subring R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance pointwise_central_scalar [MulSemiringAction Mᵐᵒᵖ R] [IsCentralScalar M R] :
    IsCentralScalar M (Subring R) :=
  ⟨fun _ S => (congr_arg fun f => S.map f) <| RingHom.ext <| op_smul_eq_smul _⟩

end Monoid

section Group

variable [Group M] [Ring R] [MulSemiringAction M R]

open scoped Pointwise

@[simp]
/-
**Subring.smul_mem_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：smul_mem_pointwise_smul_iff {a : M} {S : Subring R} {x : R} : a • x in a •
 S ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
theorem smul_mem_pointwise_smul_iff {a : M} {S : Subring R} {x : R} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff
/-
**Subring.mem_pointwise_smul_iff_inv_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring
`。
形式化陈述：mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Subring R} {x : R} : x in
 a • S ↔ a⁻¹ • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
-/
theorem mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Subring R} {x : R} :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem
/-
**Subring.mem_inv_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_inv_pointwise_smul_iff {a : M} {S : Subring R} {x : R} : x in a⁻¹ • S 
↔ a • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
-/
theorem mem_inv_pointwise_smul_iff {a : M} {S : Subring R} {x : R} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
/-
**Subring.pointwise_smul_le_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subrin
g`。
形式化陈述：pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Subring R} : a • S <= 
a • T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_smul_set_iff`：smul_set_subset_smul_set_iff : a • A s
ubseteq a • B ↔ A subseteq B
-/
theorem pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Subring R} : a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff
/-
**Subring.pointwise_smul_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：pointwise_smul_subset_iff {a : M} {S T : Subring R} : a • S <= T ↔ S <= a⁻
¹ • T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_iff_subset_inv_smul_set`：smul_set_subset_iff_subset_
inv_smul_set : a • A subseteq B ↔ A subseteq a⁻¹ • B
-/
theorem pointwise_smul_subset_iff {a : M} {S T : Subring R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  smul_set_subset_iff_subset_inv_smul_set
/-
**Subring.subset_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：subset_pointwise_smul_iff {a : M} {S T : Subring R} : S <= a • T ↔ a⁻¹ • S
 <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_smul_set_iff`：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • 
A subseteq B
-/
theorem subset_pointwise_smul_iff {a : M} {S T : Subring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_smul_set_iff

/-! TODO: add `equivSMul` like we have for subgroup. -/


end Group

section GroupWithZero

variable [GroupWithZero M] [Ring R] [MulSemiringAction M R]

open scoped Pointwise

@[simp]
/-
**Subring.smul_mem_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：smul_mem_pointwise_smul_iff {a : M} {S : Subring R} {x : R} : a • x in a •
 S ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
-/
theorem smul_mem_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subring R) (x : R) :
    a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set R) x
/-
**Subring.mem_pointwise_smul_iff_inv_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring
`。
形式化陈述：mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Subring R} {x : R} : x in
 a • S ↔ a⁻¹ • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
-/
theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : M} (ha : a ≠ 0) (S : Subring R) (x : R) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set R) x
/-
**Subring.mem_inv_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_inv_pointwise_smul_iff {a : M} {S : Subring R} {x : R} : x in a⁻¹ • S 
↔ a • x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
-/
theorem mem_inv_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subring R) (x : R) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set R) x

@[simp]
/-
**Subring.pointwise_smul_le_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subrin
g`。
形式化陈述：pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Subring R} : a • S <= 
a • T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_subset_smul_set_iff`：smul_set_subset_smul_set_iff : a • A s
ubseteq a • B ↔ A subseteq B
-/
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subring R} :
    a • S ≤ a • T ↔ S ≤ T :=
  smul_set_subset_smul_set_iff₀ ha
/-
**Subring.pointwise_smul_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_le_iff₀ {a : M} (ha : a ≠ 0) {S T : Subring R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  smul_set_subset_iff₀ ha
/-
**Subring.le_pointwise_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_smul_set_iff₀ ha

end GroupWithZero

end Subring

