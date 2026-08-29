/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Pointwise.Set.Basic

/-!
# Pointwise operations of sets in a group with zero

This file proves properties of pointwise operations of sets in a group with zero.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Ring

open Function
open scoped Pointwise

variable {α β : Type*}

namespace Set

/--
lemma `smul_set_pi₀` / 引理 `smul_set_pi₀`

English:
lemma smul_set_pi₀
  statement: {M ι : Type*} {α : ι -> Type*} [GroupWithZero M] [forall i, MulAction M (α i)]
  proof: smul_set_pi_of_isUnit (.mk0 _ hc) I s

中文:
引理 smul_set_pi₀
  结论: {M ι : 类型} {α : ι -> 类型} [带零群 M] [对任意 i, 乘法作用 M (α i)]
  证明: smul_set_pi_of_isUnit (.mk0 _ hc) I s

Depends on / 依赖: smul_set_pi_of_isUnit
-/
lemma smul_set_pi₀ {M ι : Type*} {α : ι -> Type*} [GroupWithZero M] [forall i, MulAction M (α i)]
    {c : M} (hc : c != 0) (I : Set ι) (s : forall i, Set (α i)) : c • I.pi s = I.pi (c • s) :=
  smul_set_pi_of_isUnit (.mk0 _ hc) I s

/--
lemma `smul_set_pi₀'` / 引理 `smul_set_pi₀'`

English:
lemma smul_set_pi₀'
  statement: {M ι : Type*} {α : ι -> Type*} [GroupWithZero M] [forall i, MulAction M (α i)]
  proof: h.elim (fun hc => smul_set_pi_of_isUnit (.mk0 _ hc) I s) (fun hI => hI ▸ smul_set_univ_pi ..)

中文:
引理 smul_set_pi₀'
  结论: {M ι : 类型} {α : ι -> 类型} [带零群 M] [对任意 i, 乘法作用 M (α i)]
  证明: h.elim (fun hc => smul_set_pi_of_isUnit (.mk0 _ hc) I s) (fun hI => hI ▸ smul_set_univ_pi ..)

Depends on / 依赖: h.elim, smul_set_pi_of_isUnit, smul_set_univ_pi
-/
lemma smul_set_pi₀' {M ι : Type*} {α : ι -> Type*} [GroupWithZero M] [forall i, MulAction M (α i)]
    {c : M} {I : Set ι} (h : c != 0 ∨ I = univ) (s : forall i, Set (α i)) : c • I.pi s = I.pi (c • s) :=
  h.elim (fun hc => smul_set_pi_of_isUnit (.mk0 _ hc) I s) (fun hI => hI ▸ smul_set_univ_pi ..)

section SMulZeroClass
variable [Zero β] [SMulZeroClass α β] {s : Set α} {t : Set β} {a : α}

/-- If scalar multiplication by elements of `α` sends `(0 : β)` to zero,
then the same is true for `(0 : Set β)`. -/
@[instance_reducible]
/--
Definition of `smulZeroClassSet` / `smulZeroClassSet` 的定义

English:
definition smulZeroClassSet
  signature: : SMulZeroClass α (Set β) where
  body: image_singleton.trans by rw [smul_zero, singleton_zero]

scoped[Pointwise] attribute [instance] Set.smulZeroClassSet

中文:
定义 smulZeroClassSet
  签名: : SMulZero类 α (集合 β) where
  定义体: image_singleton.trans by rw [smul_zero, singleton_zero]

scoped[Pointwise] attribute [instance] Set.smulZeroClassSet
-/
protected def smulZeroClassSet : SMulZeroClass α (Set β) where
smul_zero _ := image_singleton.trans by rw [smul_zero, singleton_zero]

scoped[Pointwise] attribute [instance] Set.smulZeroClassSet

/--
lemma `smul_zero_subset` / 引理 `smul_zero_subset`

English:
lemma smul_zero_subset
  given: (s : Set α)
  statement: s • (0 : Set β) subseteq 0
  proof: by simp [subset_def, mem_smul]

中文:
引理 smul_zero_subset
  条件: (s : 集合 α)
  结论: s • (0 : 集合 β) subseteq 0
  证明: by simp [subset_def, mem_smul]

Depends on / 依赖: mem_smul, subset_def
-/
lemma smul_zero_subset (s : Set α) : s • (0 : Set β) subseteq 0 := by simp [subset_def, mem_smul]

/--
lemma `Nonempty.smul_zero` / 引理 `Nonempty.smul_zero`

English:
lemma Nonempty.smul_zero
  given: (hs : s.Nonempty)
  statement: s • (0 : Set β) = 0
  proof: s.smul_zero_subset.antisymm by simpa [mem_smul] using! hs

中文:
引理 非空.smul_zero
  条件: (hs : s.非空)
  结论: s • (0 : 集合 β) = 0
  证明: s.smul_zero_subset.antisymm by simpa [mem_smul] using! hs
-/
lemma Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Set β) = 0 :=
s.smul_zero_subset.antisymm by simpa [mem_smul] using! hs

/--
lemma `zero_mem_smul_set` / 引理 `zero_mem_smul_set`

English:
lemma zero_mem_smul_set
  given: (h : (0 : β) in t)
  statement: (0 : β) in a • t
  proof: ⟨0, h, smul_zero _⟩

中文:
引理 zero_mem_smul_set
  条件: (h : (0 : β) in t)
  结论: (0 : β) in a • t
  证明: ⟨0, h, smul_zero _⟩

Depends on / 依赖: smul_zero
-/
lemma zero_mem_smul_set (h : (0 : β) in t) : (0 : β) in a • t := ⟨0, h, smul_zero _⟩

end SMulZeroClass
section SMulWithZero

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Set α} {t : Set β}


/--
lemma `zero_smul_subset` / 引理 `zero_smul_subset`

English:
lemma zero_smul_subset
  given: (t : Set β)
  statement: (0 : Set α) • t subseteq 0
  proof: by simp [subset_def, mem_smul]

中文:
引理 zero_smul_subset
  条件: (t : 集合 β)
  结论: (0 : 集合 α) • t subseteq 0
  证明: by simp [subset_def, mem_smul]

Depends on / 依赖: mem_smul, subset_def
-/
lemma zero_smul_subset (t : Set β) : (0 : Set α) • t subseteq 0 := by simp [subset_def, mem_smul]

/--
lemma `Nonempty.zero_smul` / 引理 `Nonempty.zero_smul`

English:
lemma Nonempty.zero_smul
  given: (ht : t.Nonempty)
  statement: (0 : Set α) • t = 0
  proof: t.zero_smul_subset.antisymm by simpa [mem_smul] using! ht

中文:
引理 非空.zero_smul
  条件: (ht : t.非空)
  结论: (0 : 集合 α) • t = 0
  证明: t.zero_smul_subset.antisymm by simpa [mem_smul] using! ht
-/
lemma Nonempty.zero_smul (ht : t.Nonempty) : (0 : Set α) • t = 0 :=
t.zero_smul_subset.antisymm by simpa [mem_smul] using! ht

/--
lemma `zero_smul_set` / 引理 `zero_smul_set`

English:
lemma zero_smul_set
  given: {s : Set β} (h : s.Nonempty)
  statement: (0 : α) • s = (0 : Set β)
  proof: by
  simp only [← image_smul, zero_smul, h.image_const, singleton_zero]

中文:
引理 zero_smul_set
  条件: {s : 集合 β} (h : s.非空)
  结论: (0 : α) • s = (0 : 集合 β)
  证明: by
  simp only [← image_smul, zero_smul, h.image_const, singleton_zero]
-/
@[simp] lemma zero_smul_set {s : Set β} (h : s.Nonempty) : (0 : α) • s = (0 : Set β) := by
  simp only [← image_smul, zero_smul, h.image_const, singleton_zero]

/--
lemma `zero_smul_set_subset` / 引理 `zero_smul_set_subset`

English:
lemma zero_smul_set_subset
  given: (s : Set β)
  statement: (0 : α) • s subseteq 0
  proof: image_subset_iff.2 fun x _ => zero_smul α x

中文:
引理 zero_smul_set_subset
  条件: (s : 集合 β)
  结论: (0 : α) • s subseteq 0
  证明: image_subset_iff.2 fun x _ => zero_smul α x

Depends on / 依赖: image_subset_iff, zero_smul
-/
lemma zero_smul_set_subset (s : Set β) : (0 : α) • s subseteq 0 :=
  image_subset_iff.2 fun x _ => zero_smul α x

/--
lemma `subsingleton_zero_smul_set` / 引理 `subsingleton_zero_smul_set`

English:
lemma subsingleton_zero_smul_set
  given: (s : Set β)
  statement: ((0 : α) • s).Subsingleton
  proof: subsingleton_singleton.anti zero_smul_set_subset s

中文:
引理 subsingleton_zero_smul_set
  条件: (s : 集合 β)
  结论: ((0 : α) • s).子单例
  证明: subsingleton_singleton.anti zero_smul_set_subset s

Depends on / 依赖: subsingleton_singleton, subsingleton_singleton.anti, zero_smul_set_subset
-/
lemma subsingleton_zero_smul_set (s : Set β) : ((0 : α) • s).Subsingleton :=
subsingleton_singleton.anti zero_smul_set_subset s

end SMulWithZero

/-- If the scalar multiplication `(· • ·) : α → β → β` is distributive,
then so is `(· • ·) : α → Set β → Set β`. -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def distribSMulSet [AddZeroClass β] [DistribSMul α β]
  body: image_image2_distrib smul_add _

scoped[Pointwise] attribute [instance] Set.distribSMulSet

中文:
定义 noncomputable
  签名: def distribSMulSet [加法零类 β] [分配标量乘法 α β]
  定义体: image_image2_distrib smul_add _

scoped[Pointwise] attribute [instance] Set.distribSMulSet
-/
protected noncomputable def distribSMulSet [AddZeroClass β] [DistribSMul α β] :
    DistribSMul α (Set β) where
smul_add _ _ _ := image_image2_distrib smul_add _

scoped[Pointwise] attribute [instance] Set.distribSMulSet

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `Set β`. -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def distribMulActionSet [Monoid α] [AddMonoid β] [DistribMulAction α β]
  body: smul_add
  smul_zero := smul_zero

中文:
定义 noncomputable
  签名: def distribMulActionSet [幺半群 α] [加法幺半群 β] [分配乘法作用 α β]
  定义体: smul_add
  smul_zero := smul_zero
-/
protected noncomputable def distribMulActionSet [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Set β) where
  smul_add := smul_add
  smul_zero := smul_zero

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `Set β`. -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mulDistribMulActionSet [Monoid α] [Monoid β] [MulDistribMulAction α β]
  body: image_image2_distrib smul_mul' _
smul_one _ := image_singleton.trans by rw [smul_one, singleton_one]

scoped[Pointwise] attribute [instance] Set.distribMulActionSet Set.mulDistribMulActionSet

中文:
定义 noncomputable
  签名: def mulDistribMulActionSet [幺半群 α] [幺半群 β] [MulDistribMul作用 α β]
  定义体: image_image2_distrib smul_mul' _
smul_one _ := image_singleton.trans by rw [smul_one, singleton_one]

scoped[Pointwise] attribute [instance] Set.distribMulActionSet Set.mulDistribMulActionSet
-/
protected noncomputable def mulDistribMulActionSet [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Set β) where
smul_mul _ _ _ := image_image2_distrib smul_mul' _
smul_one _ := image_singleton.trans by rw [smul_one, singleton_one]

scoped[Pointwise] attribute [instance] Set.distribMulActionSet Set.mulDistribMulActionSet

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Set α) where
  body: by
    by_contra! H
    have hst : (s * t).Nonempty := h.symm.subst zero_nonempty
    rw [Ne]; rw [← hst.of_smul_left.subset_zero_iff]; rw [Ne]; rw [← hst.of_smul_right.subset_zero_iff] at H
    simp only [not_subset, mem_zero] at H
    obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_z

中文:
实例 [零
  签名: α] [乘法 α] [无零因子 α] : 无零因子 (集合 α) where
  定义体: by
    by_contra! H
    have hst : (s * t).Nonempty := h.symm.subst zero_nonempty
    rw [Ne]; rw [← hst.of_smul_left.subset_zero_iff]; rw [Ne]; rw [← hst.of_smul_right.subset_zero_iff] at H
    simp only [not_subset, mem_zero] at H
    obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_z

Depends on / 依赖: Nonempty, eq_zero_or_eq_zero_of_mul_eq_zero, h.subset, h.symm.subst, hst.of_smul_left.subset_zero_iff, hst.of_smul_right.subset_zero_iff, mem_zero, mul_mem_mul, not_subset, of_smul_left, of_smul_right, subset, subset_zero_iff, zero_nonempty
-/
instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Set α) where
  eq_zero_or_eq_zero_of_mul_eq_zero {s t} h := by
    by_contra! H
    have hst : (s * t).Nonempty := h.symm.subst zero_nonempty
    rw [Ne]; rw [← hst.of_smul_left.subset_zero_iff]; rw [Ne]; rw [← hst.of_smul_right.subset_zero_iff] at H
    simp only [not_subset, mem_zero] at H
    obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_mul_eq_zero <| h.subset <| mul_mem_mul hs ht).elim ha hb

section GroupWithZero
variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

@[simp]
/--
lemma `smul_mem_smul_set_iff₀` / 引理 `smul_mem_smul_set_iff₀`

English:
lemma smul_mem_smul_set_iff₀
  given: (ha : a != 0) (A : Set β) (x : β)
  statement: a • x in a • A ↔ x in A
  proof: show Units.mk0 a ha • _ in _ ↔ _ from smul_mem_smul_set_iff

中文:
引理 smul_mem_smul_set_iff₀
  条件: (ha : a != 0) (A : 集合 β) (x : β)
  结论: a • x in a • A ↔ x in A
  证明: show Units.mk0 a ha • _ in _ ↔ _ from smul_mem_smul_set_iff

Depends on / 依赖: Units.mk0, smul_mem_smul_set_iff
-/
lemma smul_mem_smul_set_iff₀ (ha : a != 0) (A : Set β) (x : β) : a • x in a • A ↔ x in A :=
  show Units.mk0 a ha • _ in _ ↔ _ from smul_mem_smul_set_iff

/--
lemma `mem_smul_set_iff_inv_smul_mem₀` / 引理 `mem_smul_set_iff_inv_smul_mem₀`

English:
lemma mem_smul_set_iff_inv_smul_mem₀
  given: (ha : a != 0) (A : Set β) (x : β)
  statement: x in a • A ↔ a⁻¹ • x in A
  proof: show _ in Units.mk0 a ha • _ ↔ _ from mem_smul_set_iff_inv_smul_mem

中文:
引理 mem_smul_set_iff_inv_smul_mem₀
  条件: (ha : a != 0) (A : 集合 β) (x : β)
  结论: x in a • A ↔ a⁻¹ • x in A
  证明: show _ in Units.mk0 a ha • _ ↔ _ from mem_smul_set_iff_inv_smul_mem

Depends on / 依赖: Units.mk0, mem_smul_set_iff_inv_smul_mem
-/
lemma mem_smul_set_iff_inv_smul_mem₀ (ha : a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A :=
  show _ in Units.mk0 a ha • _ ↔ _ from mem_smul_set_iff_inv_smul_mem

/--
lemma `mem_inv_smul_set_iff₀` / 引理 `mem_inv_smul_set_iff₀`

English:
lemma mem_inv_smul_set_iff₀
  given: (ha : a != 0) (A : Set β) (x : β)
  statement: x in a⁻¹ • A ↔ a • x in A
  proof: show _ in (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_set_iff

中文:
引理 mem_inv_smul_set_iff₀
  条件: (ha : a != 0) (A : 集合 β) (x : β)
  结论: x in a⁻¹ • A ↔ a • x in A
  证明: show _ in (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_set_iff

Depends on / 依赖: Units.mk0, mem_inv_smul_set_iff
-/
lemma mem_inv_smul_set_iff₀ (ha : a != 0) (A : Set β) (x : β) : x in a⁻¹ • A ↔ a • x in A :=
  show _ in (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_set_iff

/--
lemma `preimage_smul₀` / 引理 `preimage_smul₀`

English:
lemma preimage_smul₀
  given: (ha : a != 0) (t : Set β)
  statement: (fun x => a • x) ⁻¹' t = a⁻¹ • t
  proof: preimage_smul (Units.mk0 a ha) t

中文:
引理 preimage_smul₀
  条件: (ha : a != 0) (t : 集合 β)
  结论: (fun x => a • x) ⁻¹' t = a⁻¹ • t
  证明: preimage_smul (Units.mk0 a ha) t

Depends on / 依赖: Units.mk0, preimage_smul
-/
lemma preimage_smul₀ (ha : a != 0) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  preimage_smul (Units.mk0 a ha) t

/--
lemma `preimage_smul_inv₀` / 引理 `preimage_smul_inv₀`

English:
lemma preimage_smul_inv₀
  given: (ha : a != 0) (t : Set β)
  statement: (fun x => a⁻¹ • x) ⁻¹' t = a • t
  proof: preimage_smul (Units.mk0 a ha)⁻¹ t

@[simp]

中文:
引理 preimage_smul_inv₀
  条件: (ha : a != 0) (t : 集合 β)
  结论: (fun x => a⁻¹ • x) ⁻¹' t = a • t
  证明: preimage_smul (Units.mk0 a ha)⁻¹ t

@[simp]

Depends on / 依赖: Units.mk0, preimage_smul
-/
lemma preimage_smul_inv₀ (ha : a != 0) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (Units.mk0 a ha)⁻¹ t

@[simp]
/--
lemma `smul_set_subset_smul_set_iff₀` / 引理 `smul_set_subset_smul_set_iff₀`

English:
lemma smul_set_subset_smul_set_iff₀
  given: (ha : a != 0) {A B : Set β}
  statement: a • A subseteq a • B ↔ A subseteq B
  proof: show Units.mk0 a ha • A subseteq _ ↔ _ from smul_set_subset_smul_set_iff

中文:
引理 smul_set_subset_smul_set_iff₀
  条件: (ha : a != 0) {A B : 集合 β}
  结论: a • A subseteq a • B ↔ A subseteq B
  证明: show Units.mk0 a ha • A subseteq _ ↔ _ from smul_set_subset_smul_set_iff

Depends on / 依赖: Units.mk0, smul_set_subset_smul_set_iff, subseteq
-/
lemma smul_set_subset_smul_set_iff₀ (ha : a != 0) {A B : Set β} : a • A subseteq a • B ↔ A subseteq B :=
  show Units.mk0 a ha • A subseteq _ ↔ _ from smul_set_subset_smul_set_iff

/--
lemma `smul_set_subset_iff₀` / 引理 `smul_set_subset_iff₀`

English:
lemma smul_set_subset_iff₀
  given: (ha : a != 0) {A B : Set β}
  statement: a • A subseteq B ↔ A subseteq a⁻¹ • B
  proof: show Units.mk0 a ha • A subseteq _ ↔ _ from smul_set_subset_iff_subset_inv_smul_set

中文:
引理 smul_set_subset_iff₀
  条件: (ha : a != 0) {A B : 集合 β}
  结论: a • A subseteq B ↔ A subseteq a⁻¹ • B
  证明: show Units.mk0 a ha • A subseteq _ ↔ _ from smul_set_subset_iff_subset_inv_smul_set

Depends on / 依赖: Units.mk0, smul_set_subset_iff_subset_inv_smul_set, subseteq
-/
lemma smul_set_subset_iff₀ (ha : a != 0) {A B : Set β} : a • A subseteq B ↔ A subseteq a⁻¹ • B :=
  show Units.mk0 a ha • A subseteq _ ↔ _ from smul_set_subset_iff_subset_inv_smul_set

/--
lemma `subset_smul_set_iff₀` / 引理 `subset_smul_set_iff₀`

English:
lemma subset_smul_set_iff₀
  given: (ha : a != 0) {A B : Set β}
  statement: A subseteq a • B ↔ a⁻¹ • A subseteq B
  proof: show _ subseteq Units.mk0 a ha • B ↔ _ from subset_smul_set_iff

中文:
引理 subset_smul_set_iff₀
  条件: (ha : a != 0) {A B : 集合 β}
  结论: A subseteq a • B ↔ a⁻¹ • A subseteq B
  证明: show _ subseteq Units.mk0 a ha • B ↔ _ from subset_smul_set_iff

Depends on / 依赖: Units.mk0, subset_smul_set_iff, subseteq
-/
lemma subset_smul_set_iff₀ (ha : a != 0) {A B : Set β} : A subseteq a • B ↔ a⁻¹ • A subseteq B :=
  show _ subseteq Units.mk0 a ha • B ↔ _ from subset_smul_set_iff

/--
lemma `smul_set_inter₀` / 引理 `smul_set_inter₀`

English:
lemma smul_set_inter₀
  given: (ha : a != 0)
  statement: a • (s inter t) = a • s inter a • t
  proof: show Units.mk0 a ha • _ = _ from smul_set_inter

中文:
引理 smul_set_inter₀
  条件: (ha : a != 0)
  结论: a • (s inter t) = a • s inter a • t
  证明: show Units.mk0 a ha • _ = _ from smul_set_inter

Depends on / 依赖: Units.mk0, smul_set_inter
-/
lemma smul_set_inter₀ (ha : a != 0) : a • (s inter t) = a • s inter a • t :=
  show Units.mk0 a ha • _ = _ from smul_set_inter

/--
lemma `smul_set_sdiff₀` / 引理 `smul_set_sdiff₀`

English:
lemma smul_set_sdiff₀
  given: (ha : a != 0)
  statement: a • (s \ t) = a • s \ a • t
  proof: image_sdiff (MulAction.injective₀ ha) _ _

中文:
引理 smul_set_sdiff₀
  条件: (ha : a != 0)
  结论: a • (s \ t) = a • s \ a • t
  证明: image_sdiff (MulAction.injective₀ ha) _ _

Depends on / 依赖: MulAction, MulAction.injective, image_sdiff
-/
lemma smul_set_sdiff₀ (ha : a != 0) : a • (s \ t) = a • s \ a • t :=
  image_sdiff (MulAction.injective₀ ha) _ _

open scoped symmDiff in
/--
lemma `smul_set_symmDiff₀` / 引理 `smul_set_symmDiff₀`

English:
lemma smul_set_symmDiff₀
  given: (ha : a != 0)
  statement: a • s ∆ t = (a • s) ∆ (a • t)
  proof: image_symmDiff (MulAction.injective₀ ha) _ _

中文:
引理 smul_set_symmDiff₀
  条件: (ha : a != 0)
  结论: a • s ∆ t = (a • s) ∆ (a • t)
  证明: image_symmDiff (MulAction.injective₀ ha) _ _

Depends on / 依赖: MulAction, MulAction.injective, image_symmDiff
-/
lemma smul_set_symmDiff₀ (ha : a != 0) : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff (MulAction.injective₀ ha) _ _

/--
lemma `smul_set_univ₀` / 引理 `smul_set_univ₀`

English:
lemma smul_set_univ₀
  given: (ha : a != 0)
  statement: a • (univ : Set β) = univ
  proof: image_univ_of_surjective MulAction.surjective₀ ha

中文:
引理 smul_set_univ₀
  条件: (ha : a != 0)
  结论: a • (univ : 集合 β) = univ
  证明: image_univ_of_surjective MulAction.surjective₀ ha

Depends on / 依赖: MulAction, MulAction.surjective, image_univ_of_surjective
-/
lemma smul_set_univ₀ (ha : a != 0) : a • (univ : Set β) = univ :=
image_univ_of_surjective MulAction.surjective₀ ha

/--
lemma `smul_univ₀` / 引理 `smul_univ₀`

English:
lemma smul_univ₀
  given: {s : Set α} (hs : ¬s subseteq 0)
  statement: s • (univ : Set β) = univ
  proof: let ⟨a, ha, ha₀⟩ := not_subset.1 hs
  eq_univ_of_forall fun b => ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul₀ ha₀ _⟩

中文:
引理 smul_univ₀
  条件: {s : 集合 α} (hs : ¬s subseteq 0)
  结论: s • (univ : 集合 β) = univ
  证明: let ⟨a, ha, ha₀⟩ := not_subset.1 hs
  eq_univ_of_forall fun b => ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul₀ ha₀ _⟩

Depends on / 依赖: eq_univ_of_forall, not_subset
-/
lemma smul_univ₀ {s : Set α} (hs : ¬s subseteq 0) : s • (univ : Set β) = univ :=
  let ⟨a, ha, ha₀⟩ := not_subset.1 hs
  eq_univ_of_forall fun b => ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul₀ ha₀ _⟩

/--
lemma `smul_univ₀'` / 引理 `smul_univ₀'`

English:
lemma smul_univ₀'
  given: {s : Set α} (hs : s.Nontrivial)
  statement: s • (univ : Set β) = univ
  proof: smul_univ₀ hs.not_subset_singleton

中文:
引理 smul_univ₀'
  条件: {s : 集合 α} (hs : s.非平凡)
  结论: s • (univ : 集合 β) = univ
  证明: smul_univ₀ hs.not_subset_singleton

Depends on / 依赖: hs.not_subset_singleton, not_subset_singleton
-/
lemma smul_univ₀' {s : Set α} (hs : s.Nontrivial) : s • (univ : Set β) = univ :=
  smul_univ₀ hs.not_subset_singleton

open scoped RightActions in
/--
lemma `inv_smul_set_distrib₀` / 引理 `inv_smul_set_distrib₀`

English:
lemma inv_smul_set_distrib₀
  given: (a : α) (s : Set α)
  statement: (a • s)⁻¹ = s⁻¹ <• a⁻¹
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [mem_smul_set_iff_inv_smul_mem₀, *]

中文:
引理 inv_smul_set_distrib₀
  条件: (a : α) (s : 集合 α)
  结论: (a • s)⁻¹ = s⁻¹ <• a⁻¹
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [mem_smul_set_iff_inv_smul_mem₀, *]
-/
@[simp] lemma inv_smul_set_distrib₀ (a : α) (s : Set α) : (a • s)⁻¹ = s⁻¹ <• a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [mem_smul_set_iff_inv_smul_mem₀, *]

open scoped RightActions in
/--
lemma `inv_op_smul_set_distrib₀` / 引理 `inv_op_smul_set_distrib₀`

English:
lemma inv_op_smul_set_distrib₀
  given: (a : α) (s : Set α)
  statement: (s <• a)⁻¹ = a⁻¹ • s⁻¹
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [mem_smul_set_iff_inv_smul_mem₀, *]

中文:
引理 inv_op_smul_set_distrib₀
  条件: (a : α) (s : 集合 α)
  结论: (s <• a)⁻¹ = a⁻¹ • s⁻¹
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [mem_smul_set_iff_inv_smul_mem₀, *]
-/
@[simp] lemma inv_op_smul_set_distrib₀ (a : α) (s : Set α) : (s <• a)⁻¹ = a⁻¹ • s⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · obtain rfl | hs := s.eq_empty_or_nonempty <;> simp [*]
  · ext; simp [mem_smul_set_iff_inv_smul_mem₀, *]

end GroupWithZero
end Set
