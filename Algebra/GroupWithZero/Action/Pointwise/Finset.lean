/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.GroupWithZero.Pointwise.Finset

/-!
# Pointwise operations of finsets in a group with zero

This file proves properties of pointwise operations of finsets in a group with zero.
-/

@[expose] public section

assert_not_exists Ring

open scoped Pointwise

namespace Finset
variable {α β : Type*} [DecidableEq β]

/-- If scalar multiplication by elements of `α` sends `(0 : β)` to zero,
then the same is true for `(0 : Finset β)`. -/
@[instance_reducible]
/--
Definition of `smulZeroClass` / `smulZeroClass` 的定义

English:
definition smulZeroClass
  signature: [Zero β] [SMulZeroClass α β]
  body: coe_injective.smulZeroClass ⟨_, coe_zero⟩ coe_smul_finset

中文:
定义 smulZeroClass
  签名: [零 β] [SMulZero类 α β]
  定义体: coe_injective.smulZeroClass ⟨_, coe_zero⟩ coe_smul_finset
-/
protected def smulZeroClass [Zero β] [SMulZeroClass α β] : SMulZeroClass α (Finset β) :=
  coe_injective.smulZeroClass ⟨_, coe_zero⟩ coe_smul_finset

/-- If the scalar multiplication `(· • ·) : α → β → β` is distributive,
then so is `(· • ·) : α → Finset β → Finset β`. -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def distribSMul [AddZeroClass β] [DistribSMul α β]
  body: coe_injective.distribSMul coeAddMonoidHom coe_smul_finset

中文:
定义 noncomputable
  签名: def distribSMul [加法零类 β] [分配标量乘法 α β]
  定义体: coe_injective.distribSMul coeAddMonoidHom coe_smul_finset
-/
protected noncomputable def distribSMul [AddZeroClass β] [DistribSMul α β] :
    DistribSMul α (Finset β) :=
  coe_injective.distribSMul coeAddMonoidHom coe_smul_finset

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `Finset β`. -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def distribMulAction [Monoid α] [AddMonoid β] [DistribMulAction α β]
  body: coe_injective.distribMulAction coeAddMonoidHom coe_smul_finset

中文:
定义 noncomputable
  签名: def distribMulAction [幺半群 α] [加法幺半群 β] [分配乘法作用 α β]
  定义体: coe_injective.distribMulAction coeAddMonoidHom coe_smul_finset
-/
protected noncomputable def distribMulAction [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Finset β) :=
  coe_injective.distribMulAction coeAddMonoidHom coe_smul_finset

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `Set β`. -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mulDistribMulAction [Monoid α] [Monoid β] [MulDistribMulAction α β]
  body: coe_injective.mulDistribMulAction coeMonoidHom coe_smul_finset

scoped[Pointwise] attribute [instance] Finset.smulZeroClass Finset.distribSMul
  Finset.distribMulAction Finset.mulDistribMulAction

中文:
定义 noncomputable
  签名: def mulDistribMulAction [幺半群 α] [幺半群 β] [MulDistribMul作用 α β]
  定义体: coe_injective.mulDistribMulAction coeMonoidHom coe_smul_finset

scoped[Pointwise] attribute [instance] Finset.smulZeroClass Finset.distribSMul
  Finset.distribMulAction Finset.mulDistribMulAction
-/
protected noncomputable def mulDistribMulAction [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Finset β) :=
  coe_injective.mulDistribMulAction coeMonoidHom coe_smul_finset

scoped[Pointwise] attribute [instance] Finset.smulZeroClass Finset.distribSMul
  Finset.distribMulAction Finset.mulDistribMulAction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Finset α)
  body: Function.Injective.noZeroDivisors _ coe_injective coe_zero coe_mul

中文:
实例 [DecidableEq
  签名: α] [零 α] [乘法 α] [无零因子 α] : 无零因子 (有限集 α)
  定义体: Function.Injective.noZeroDivisors _ coe_injective coe_zero coe_mul

Depends on / 依赖: Function, Function.Injective.noZeroDivisors, Injective, coe_injective, coe_mul, coe_zero, noZeroDivisors
-/
instance [DecidableEq α] [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Finset α) :=
  Function.Injective.noZeroDivisors _ coe_injective coe_zero coe_mul

section SMulZeroClass
variable [Zero β] [SMulZeroClass α β] {s : Finset α} {t : Finset β} {a : α}

/--
lemma `smul_zero_subset` / 引理 `smul_zero_subset`

English:
lemma smul_zero_subset
  given: (s : Finset α)
  statement: s • (0 : Finset β) subseteq 0
  proof: by simp [subset_iff, mem_smul]

中文:
引理 smul_zero_subset
  条件: (s : 有限集 α)
  结论: s • (0 : 有限集 β) subseteq 0
  证明: by simp [subset_iff, mem_smul]

Depends on / 依赖: mem_smul, subset_iff
-/
lemma smul_zero_subset (s : Finset α) : s • (0 : Finset β) subseteq 0 := by simp [subset_iff, mem_smul]

/--
lemma `Nonempty.smul_zero` / 引理 `Nonempty.smul_zero`

English:
lemma Nonempty.smul_zero
  given: (hs : s.Nonempty)
  statement: s • (0 : Finset β) = 0
  proof: s.smul_zero_subset.antisymm by simpa [mem_smul] using! hs

中文:
引理 非空.smul_zero
  条件: (hs : s.非空)
  结论: s • (0 : 有限集 β) = 0
  证明: s.smul_zero_subset.antisymm by simpa [mem_smul] using! hs

Depends on / 依赖: antisymm, mem_smul, s.smul_zero_subset.antisymm, smul_zero_subset
-/
lemma Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Finset β) = 0 :=
s.smul_zero_subset.antisymm by simpa [mem_smul] using! hs

/--
lemma `zero_mem_smul_finset` / 引理 `zero_mem_smul_finset`

English:
lemma zero_mem_smul_finset
  given: (h : (0 : β) in t)
  statement: (0 : β) in a • t
  proof: mem_smul_finset.2 ⟨0, h, smul_zero _⟩

中文:
引理 zero_mem_smul_finset
  条件: (h : (0 : β) in t)
  结论: (0 : β) in a • t
  证明: mem_smul_finset.2 ⟨0, h, smul_zero _⟩

Depends on / 依赖: mem_smul_finset, smul_zero
-/
lemma zero_mem_smul_finset (h : (0 : β) in t) : (0 : β) in a • t :=
  mem_smul_finset.2 ⟨0, h, smul_zero _⟩

end SMulZeroClass

section SMulWithZero
variable [Zero α] [Zero β] [SMulWithZero α β] {s : Finset α} {t : Finset β}


/--
lemma `zero_smul_subset` / 引理 `zero_smul_subset`

English:
lemma zero_smul_subset
  given: (t : Finset β)
  statement: (0 : Finset α) • t subseteq 0
  proof: by simp [subset_iff, mem_smul]

中文:
引理 zero_smul_subset
  条件: (t : 有限集 β)
  结论: (0 : 有限集 α) • t subseteq 0
  证明: by simp [subset_iff, mem_smul]

Depends on / 依赖: mem_smul, subset_iff
-/
lemma zero_smul_subset (t : Finset β) : (0 : Finset α) • t subseteq 0 := by simp [subset_iff, mem_smul]

/--
lemma `Nonempty.zero_smul` / 引理 `Nonempty.zero_smul`

English:
lemma Nonempty.zero_smul
  given: (ht : t.Nonempty)
  statement: (0 : Finset α) • t = 0
  proof: t.zero_smul_subset.antisymm by simpa [mem_smul] using! ht

中文:
引理 非空.zero_smul
  条件: (ht : t.非空)
  结论: (0 : 有限集 α) • t = 0
  证明: t.zero_smul_subset.antisymm by simpa [mem_smul] using! ht

Depends on / 依赖: antisymm, mem_smul, t.zero_smul_subset.antisymm, zero_smul_subset
-/
lemma Nonempty.zero_smul (ht : t.Nonempty) : (0 : Finset α) • t = 0 :=
t.zero_smul_subset.antisymm by simpa [mem_smul] using! ht

/--
lemma `zero_smul_finset` / 引理 `zero_smul_finset`

English:
lemma zero_smul_finset
  given: {s : Finset β} (h : s.Nonempty)
  statement: (0 : α) • s = (0 : Finset β)
  proof: coe_injective by simpa using @Set.zero_smul_set α _ _ _ _ _ h

中文:
引理 zero_smul_finset
  条件: {s : 有限集 β} (h : s.非空)
  结论: (0 : α) • s = (0 : 有限集 β)
  证明: coe_injective by simpa using @Set.zero_smul_set α _ _ _ _ _ h
-/
@[simp] lemma zero_smul_finset {s : Finset β} (h : s.Nonempty) : (0 : α) • s = (0 : Finset β) :=
coe_injective by simpa using @Set.zero_smul_set α _ _ _ _ _ h

/--
lemma `zero_smul_finset_subset` / 引理 `zero_smul_finset_subset`

English:
lemma zero_smul_finset_subset
  given: (s : Finset β)
  statement: (0 : α) • s subseteq 0
  proof: image_subset_iff.2 fun x _ => mem_zero.2 zero_smul α x

中文:
引理 zero_smul_finset_subset
  条件: (s : 有限集 β)
  结论: (0 : α) • s subseteq 0
  证明: image_subset_iff.2 fun x _ => mem_zero.2 zero_smul α x

Depends on / 依赖: image_subset_iff, mem_zero, zero_smul
-/
lemma zero_smul_finset_subset (s : Finset β) : (0 : α) • s subseteq 0 :=
image_subset_iff.2 fun x _ => mem_zero.2 zero_smul α x

end SMulWithZero

section GroupWithZero
variable [GroupWithZero α]

section MulAction
variable [MulAction α β] {s t : Finset β} {a : α} {b : β}

/--
lemma `smul_mem_smul_finset_iff₀` / 引理 `smul_mem_smul_finset_iff₀`

English:
lemma smul_mem_smul_finset_iff₀
  given: (ha : a != 0)
  statement: a • b in a • s ↔ b in s
  proof: smul_mem_smul_finset_iff (Units.mk0 a ha)

中文:
引理 smul_mem_smul_finset_iff₀
  条件: (ha : a != 0)
  结论: a • b in a • s ↔ b in s
  证明: smul_mem_smul_finset_iff (Units.mk0 a ha)
-/
@[simp] lemma smul_mem_smul_finset_iff₀ (ha : a != 0) : a • b in a • s ↔ b in s :=
  smul_mem_smul_finset_iff (Units.mk0 a ha)

/--
lemma `inv_smul_mem_iff₀` / 引理 `inv_smul_mem_iff₀`

English:
lemma inv_smul_mem_iff₀
  given: (ha : a != 0)
  statement: a⁻¹ • b in s ↔ b in a • s
  proof: show _ ↔ _ in Units.mk0 a ha • _ from inv_smul_mem_iff

中文:
引理 inv_smul_mem_iff₀
  条件: (ha : a != 0)
  结论: a⁻¹ • b in s ↔ b in a • s
  证明: show _ ↔ _ in Units.mk0 a ha • _ from inv_smul_mem_iff

Depends on / 依赖: Units.mk0, inv_smul_mem_iff
-/
lemma inv_smul_mem_iff₀ (ha : a != 0) : a⁻¹ • b in s ↔ b in a • s :=
  show _ ↔ _ in Units.mk0 a ha • _ from inv_smul_mem_iff

/--
lemma `mem_inv_smul_finset_iff₀` / 引理 `mem_inv_smul_finset_iff₀`

English:
lemma mem_inv_smul_finset_iff₀
  given: (ha : a != 0)
  statement: b in a⁻¹ • s ↔ a • b in s
  proof: show _ in (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_finset_iff

@[simp]

中文:
引理 mem_inv_smul_finset_iff₀
  条件: (ha : a != 0)
  结论: b in a⁻¹ • s ↔ a • b in s
  证明: show _ in (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_finset_iff

@[simp]

Depends on / 依赖: Units.mk0, mem_inv_smul_finset_iff
-/
lemma mem_inv_smul_finset_iff₀ (ha : a != 0) : b in a⁻¹ • s ↔ a • b in s :=
  show _ in (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_finset_iff

@[simp]
/--
lemma `smul_finset_subset_smul_finset_iff₀` / 引理 `smul_finset_subset_smul_finset_iff₀`

English:
lemma smul_finset_subset_smul_finset_iff₀
  given: (ha : a != 0)
  statement: a • s subseteq a • t ↔ s subseteq t
  proof: show Units.mk0 a ha • s subseteq _ ↔ _ from smul_finset_subset_smul_finset_iff

中文:
引理 smul_finset_subset_smul_finset_iff₀
  条件: (ha : a != 0)
  结论: a • s subseteq a • t ↔ s subseteq t
  证明: show Units.mk0 a ha • s subseteq _ ↔ _ from smul_finset_subset_smul_finset_iff

Depends on / 依赖: Units.mk0, smul_finset_subset_smul_finset_iff, subseteq
-/
lemma smul_finset_subset_smul_finset_iff₀ (ha : a != 0) : a • s subseteq a • t ↔ s subseteq t :=
  show Units.mk0 a ha • s subseteq _ ↔ _ from smul_finset_subset_smul_finset_iff

/--
theorem `pairwiseDisjoint_smul_iff₀` / 定理 `pairwiseDisjoint_smul_iff₀`

English:
theorem pairwiseDisjoint_smul_iff₀
  given: {s : Set α} {t : Finset β} (hs : forall a in s, a != 0)
  proof: by
  simp_rw [← pairwiseDisjoint_coe, coe_smul_finset]
  exact Set.pairwiseDisjoint_image_right_iff (fun a ha => MulAction.injective₀ (hs a ha))

中文:
定理 pairwiseDisjoint_smul_iff₀
  条件: {s : 集合 α} {t : 有限集 β} (hs : 对任意 a in s, a != 0)
  证明: by
  simp_rw [← pairwiseDisjoint_coe, coe_smul_finset]
  exact Set.pairwiseDisjoint_image_right_iff (fun a ha => MulAction.injective₀ (hs a ha))

Depends on / 依赖: MulAction, MulAction.injective, Set.pairwiseDisjoint_image_right_iff, coe_smul_finset, pairwiseDisjoint_coe, pairwiseDisjoint_image_right_iff, simp_rw
-/
theorem pairwiseDisjoint_smul_iff₀ {s : Set α} {t : Finset β} (hs : forall a in s, a != 0) :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t : Set (α × β)).InjOn fun p => p.1 • p.2 := by
  simp_rw [← pairwiseDisjoint_coe, coe_smul_finset]
  exact Set.pairwiseDisjoint_image_right_iff (fun a ha => MulAction.injective₀ (hs a ha))

/--
lemma `smul_finset_subset_iff₀` / 引理 `smul_finset_subset_iff₀`

English:
lemma smul_finset_subset_iff₀
  given: (ha : a != 0)
  statement: a • s subseteq t ↔ s subseteq a⁻¹ • t
  proof: show Units.mk0 a ha • s subseteq _ ↔ _ from smul_finset_subset_iff

中文:
引理 smul_finset_subset_iff₀
  条件: (ha : a != 0)
  结论: a • s subseteq t ↔ s subseteq a⁻¹ • t
  证明: show Units.mk0 a ha • s subseteq _ ↔ _ from smul_finset_subset_iff

Depends on / 依赖: Units.mk0, smul_finset_subset_iff, subseteq
-/
lemma smul_finset_subset_iff₀ (ha : a != 0) : a • s subseteq t ↔ s subseteq a⁻¹ • t :=
  show Units.mk0 a ha • s subseteq _ ↔ _ from smul_finset_subset_iff

/--
lemma `subset_smul_finset_iff₀` / 引理 `subset_smul_finset_iff₀`

English:
lemma subset_smul_finset_iff₀
  given: (ha : a != 0)
  statement: s subseteq a • t ↔ a⁻¹ • s subseteq t
  proof: show _ subseteq Units.mk0 a ha • t ↔ _ from subset_smul_finset_iff

中文:
引理 subset_smul_finset_iff₀
  条件: (ha : a != 0)
  结论: s subseteq a • t ↔ a⁻¹ • s subseteq t
  证明: show _ subseteq Units.mk0 a ha • t ↔ _ from subset_smul_finset_iff

Depends on / 依赖: Units.mk0, subset_smul_finset_iff, subseteq
-/
lemma subset_smul_finset_iff₀ (ha : a != 0) : s subseteq a • t ↔ a⁻¹ • s subseteq t :=
  show _ subseteq Units.mk0 a ha • t ↔ _ from subset_smul_finset_iff

/--
lemma `smul_finset_inter₀` / 引理 `smul_finset_inter₀`

English:
lemma smul_finset_inter₀
  given: (ha : a != 0)
  statement: a • (s inter t) = a • s inter a • t
  proof: image_inter _ _ MulAction.injective₀ ha

中文:
引理 smul_finset_inter₀
  条件: (ha : a != 0)
  结论: a • (s inter t) = a • s inter a • t
  证明: image_inter _ _ MulAction.injective₀ ha

Depends on / 依赖: MulAction, MulAction.injective, image_inter
-/
lemma smul_finset_inter₀ (ha : a != 0) : a • (s inter t) = a • s inter a • t :=
image_inter _ _ MulAction.injective₀ ha

/--
lemma `smul_finset_sdiff₀` / 引理 `smul_finset_sdiff₀`

English:
lemma smul_finset_sdiff₀
  given: (ha : a != 0)
  statement: a • (s \ t) = a • s \ a • t
  proof: image_sdiff _ _ MulAction.injective₀ ha

中文:
引理 smul_finset_sdiff₀
  条件: (ha : a != 0)
  结论: a • (s \ t) = a • s \ a • t
  证明: image_sdiff _ _ MulAction.injective₀ ha

Depends on / 依赖: MulAction, MulAction.injective, image_sdiff
-/
lemma smul_finset_sdiff₀ (ha : a != 0) : a • (s \ t) = a • s \ a • t :=
image_sdiff _ _ MulAction.injective₀ ha

open scoped symmDiff in
/--
lemma `smul_finset_symmDiff₀` / 引理 `smul_finset_symmDiff₀`

English:
lemma smul_finset_symmDiff₀
  given: (ha : a != 0)
  statement: a • s ∆ t = (a • s) ∆ (a • t)
  proof: image_symmDiff _ _ MulAction.injective₀ ha

中文:
引理 smul_finset_symmDiff₀
  条件: (ha : a != 0)
  结论: a • s ∆ t = (a • s) ∆ (a • t)
  证明: image_symmDiff _ _ MulAction.injective₀ ha

Depends on / 依赖: MulAction, MulAction.injective, image_symmDiff
-/
lemma smul_finset_symmDiff₀ (ha : a != 0) : a • s ∆ t = (a • s) ∆ (a • t) :=
image_symmDiff _ _ MulAction.injective₀ ha

/--
lemma `smul_finset_univ₀` / 引理 `smul_finset_univ₀`

English:
lemma smul_finset_univ₀
  given: [Fintype β] (ha : a != 0)
  statement: a • (univ : Finset β) = univ
  proof: coe_injective by push_cast; exact Set.smul_set_univ₀ ha

@[simp]

中文:
引理 smul_finset_univ₀
  条件: [有限类型 β] (ha : a != 0)
  结论: a • (univ : 有限集 β) = univ
  证明: coe_injective by push_cast; exact Set.smul_set_univ₀ ha

@[simp]

Depends on / 依赖: Set.smul_set_univ, coe_injective
-/
lemma smul_finset_univ₀ [Fintype β] (ha : a != 0) : a • (univ : Finset β) = univ :=
coe_injective by push_cast; exact Set.smul_set_univ₀ ha

@[simp]
/--
lemma `smul_finset_eq_univ₀` / 引理 `smul_finset_eq_univ₀`

English:
lemma smul_finset_eq_univ₀
  given: [Fintype β] (ha : a != 0)
  statement: a • s = univ ↔ s = univ
  proof: by
  exact_mod_cast smul_finset_eq_univ (α := Units α) (a := Units.mk0 a ha)

中文:
引理 smul_finset_eq_univ₀
  条件: [有限类型 β] (ha : a != 0)
  结论: a • s = univ ↔ s = univ
  证明: by
  exact_mod_cast smul_finset_eq_univ (α := Units α) (a := Units.mk0 a ha)

Depends on / 依赖: Units.mk0, smul_finset_eq_univ
-/
lemma smul_finset_eq_univ₀ [Fintype β] (ha : a != 0) : a • s = univ ↔ s = univ := by
  exact_mod_cast smul_finset_eq_univ (α := Units α) (a := Units.mk0 a ha)

/--
lemma `smul_univ₀` / 引理 `smul_univ₀`

English:
lemma smul_univ₀
  given: [Fintype β] {s : Finset α} (hs : ¬s subseteq 0)
  statement: s • (univ : Finset β) = univ
  proof: coe_injective by
    rw [← coe_subset] at hs
    push_cast at hs ⊢
    exact Set.smul_univ₀ hs

中文:
引理 smul_univ₀
  条件: [有限类型 β] {s : 有限集 α} (hs : ¬s subseteq 0)
  结论: s • (univ : 有限集 β) = univ
  证明: coe_injective by
    rw [← coe_subset] at hs
    push_cast at hs ⊢
    exact Set.smul_univ₀ hs

Depends on / 依赖: Set.smul_univ, coe_injective, coe_subset
-/
lemma smul_univ₀ [Fintype β] {s : Finset α} (hs : ¬s subseteq 0) : s • (univ : Finset β) = univ :=
coe_injective by
    rw [← coe_subset] at hs
    push_cast at hs ⊢
    exact Set.smul_univ₀ hs

/--
lemma `smul_univ₀'` / 引理 `smul_univ₀'`

English:
lemma smul_univ₀'
  given: [Fintype β] {s : Finset α} (hs : s.Nontrivial)
  statement: s • (univ : Finset β) = univ
  proof: coe_injective by push_cast; exact Set.smul_univ₀' hs

@[simp]

中文:
引理 smul_univ₀'
  条件: [有限类型 β] {s : 有限集 α} (hs : s.非平凡)
  结论: s • (univ : 有限集 β) = univ
  证明: coe_injective by push_cast; exact Set.smul_univ₀' hs

@[simp]

Depends on / 依赖: Set.smul_univ, coe_injective
-/
lemma smul_univ₀' [Fintype β] {s : Finset α} (hs : s.Nontrivial) : s • (univ : Finset β) = univ :=
coe_injective by push_cast; exact Set.smul_univ₀' hs

@[simp]
/--
lemma `card_smul_finset₀` / 引理 `card_smul_finset₀`

English:
lemma card_smul_finset₀
  given: (ha : a != 0) (s : Finset β)
  statement: (a • s).card = s.card
  proof: card_image_of_injective _ (MulAction.injective₀ ha)

中文:
引理 card_smul_finset₀
  条件: (ha : a != 0) (s : 有限集 β)
  结论: (a • s).card = s.card
  证明: card_image_of_injective _ (MulAction.injective₀ ha)

Depends on / 依赖: MulAction, MulAction.injective, card_image_of_injective
-/
lemma card_smul_finset₀ (ha : a != 0) (s : Finset β) : (a • s).card = s.card :=
  card_image_of_injective _ (MulAction.injective₀ ha)

/--
lemma `card_dvd_card_smul_right₀` / 引理 `card_dvd_card_smul_right₀`

English:
lemma card_dvd_card_smul_right₀
  given: {s : Finset α} (hs : forall a in s, a != 0)
  proof: card_dvd_card_image₂_right fun a ha => MulAction.injective₀ (hs a ha)

中文:
引理 card_dvd_card_smul_right₀
  条件: {s : 有限集 α} (hs : 对任意 a in s, a != 0)
  证明: card_dvd_card_image₂_right fun a ha => MulAction.injective₀ (hs a ha)

Depends on / 依赖: MulAction, MulAction.injective
-/
lemma card_dvd_card_smul_right₀ {s : Finset α} (hs : forall a in s, a != 0) :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id -> t.card ∣ (s • t).card :=
  card_dvd_card_image₂_right fun a ha => MulAction.injective₀ (hs a ha)

end MulAction

variable [DecidableEq α] {s : Finset α}

open scoped RightActions

/--
lemma `inv_smul_finset_distrib₀` / 引理 `inv_smul_finset_distrib₀`

English:
lemma inv_smul_finset_distrib₀
  given: (a : α) (s : Finset α)
  statement: (a • s)⁻¹ = s⁻¹ <• a⁻¹
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  · ext; simp only [mem_inv', ne_eq, not_false_eq_true, ← inv_smul_mem_iff₀, smul_eq_mul,
      MulOpposite.op_inv, inv_eq_zero, MulOpposite.op_eq_zero_iff, inv_inv,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_inv_rev, ha]

中文:
引理 inv_smul_finset_distrib₀
  条件: (a : α) (s : 有限集 α)
  结论: (a • s)⁻¹ = s⁻¹ <• a⁻¹
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  · ext; simp only [mem_inv', ne_eq, not_false_eq_true, ← inv_smul_mem_iff₀, smul_eq_mul,
      MulOpposite.op_inv, inv_eq_zero, MulOpposite.op_eq_zero_iff, inv_inv,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_inv_rev, ha]
-/
@[simp] lemma inv_smul_finset_distrib₀ (a : α) (s : Finset α) : (a • s)⁻¹ = s⁻¹ <• a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  · ext; simp only [mem_inv', ne_eq, not_false_eq_true, ← inv_smul_mem_iff₀, smul_eq_mul,
      MulOpposite.op_inv, inv_eq_zero, MulOpposite.op_eq_zero_iff, inv_inv,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_inv_rev, ha]

/--
lemma `inv_op_smul_finset_distrib₀` / 引理 `inv_op_smul_finset_distrib₀`

English:
lemma inv_op_smul_finset_distrib₀
  given: (a : α) (s : Finset α)
  statement: (s <• a)⁻¹ = a⁻¹ • s⁻¹
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  · ext; simp only [mem_inv', ne_eq, MulOpposite.op_eq_zero_iff, not_false_eq_true, ←
      inv_smul_mem_iff₀, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_inv, MulOpposite.unop_op,
      inv_eq_zero, inv_inv, smul_eq_mul, mul_inv_rev, ha]

中文:
引理 inv_op_smul_finset_distrib₀
  条件: (a : α) (s : 有限集 α)
  结论: (s <• a)⁻¹ = a⁻¹ • s⁻¹
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  · ext; simp only [mem_inv', ne_eq, MulOpposite.op_eq_zero_iff, not_false_eq_true, ←
      inv_smul_mem_iff₀, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_inv, MulOpposite.unop_op,
      inv_eq_zero, inv_inv, smul_eq_mul, mul_inv_rev, ha]

Depends on / 依赖: eq_empty_or_nonempty, eq_or_ne, s.eq_empty_or_nonempty
-/
lemma inv_op_smul_finset_distrib₀ (a : α) (s : Finset α) : (s <• a)⁻¹ = a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  -- was `simp` and very slow (https://github.com/leanprover-community/mathlib4/issues/19751)
  · ext; simp only [mem_inv', ne_eq, MulOpposite.op_eq_zero_iff, not_false_eq_true, ←
      inv_smul_mem_iff₀, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_inv, MulOpposite.unop_op,
      inv_eq_zero, inv_inv, smul_eq_mul, mul_inv_rev, ha]

end GroupWithZero

section Monoid
variable [Monoid α] [AddGroup β] [DistribMulAction α β]

@[simp]
/--
lemma `smul_finset_neg` / 引理 `smul_finset_neg`

English:
lemma smul_finset_neg
  given: (a : α) (t : Finset β)
  statement: a • -t = -(a • t)
  proof: by
  simp only [← image_smul, ← image_neg_eq_neg, Function.comp_def, image_image, smul_neg]

@[simp]

中文:
引理 smul_finset_neg
  条件: (a : α) (t : 有限集 β)
  结论: a • -t = -(a • t)
  证明: by
  simp only [← image_smul, ← image_neg_eq_neg, Function.comp_def, image_image, smul_neg]

@[simp]

Depends on / 依赖: Function, Function.comp_def, comp_def, image_image, image_neg_eq_neg, image_smul, smul_neg
-/
lemma smul_finset_neg (a : α) (t : Finset β) : a • -t = -(a • t) := by
  simp only [← image_smul, ← image_neg_eq_neg, Function.comp_def, image_image, smul_neg]

@[simp]
/--
lemma `smul_neg` / 引理 `smul_neg`

English:
lemma smul_neg
  given: (s : Finset α) (t : Finset β)
  statement: s • -t = -(s • t)
  proof: by
  simp_rw [← image_neg_eq_neg]; exact image_image₂_right_comm smul_neg

中文:
引理 smul_neg
  条件: (s : 有限集 α) (t : 有限集 β)
  结论: s • -t = -(s • t)
  证明: by
  simp_rw [← image_neg_eq_neg]; exact image_image₂_right_comm smul_neg
-/
protected lemma smul_neg (s : Finset α) (t : Finset β) : s • -t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]; exact image_image₂_right_comm smul_neg

end Monoid
end Finset
