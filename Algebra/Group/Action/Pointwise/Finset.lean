/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Pointwise actions of finsets
-/

@[expose] public section

-- TODO
-- assert_not_exists MonoidWithZero
assert_not_exists Cardinal

open Function MulOpposite

open scoped Pointwise

variable {F α β γ : Type*}

namespace Finset

/-! ### Instances -/

section Instances

variable [DecidableEq γ]

@[to_additive]
/--
Instance `smulCommClass_finset` / 实例 `smulCommClass_finset`

English:
instance smulCommClass_finset
  signature: [SMul α γ] [SMul β γ] [SMulCommClass α β γ]
  body: ⟨fun _ _ => Commute.finset_image smul_comm _ _⟩

@[to_additive]

中文:
实例 smulCommClass_finset
  签名: [标量乘法 α γ] [标量乘法 β γ] [标量交换类 α β γ]
  定义体: ⟨fun _ _ => Commute.finset_image smul_comm _ _⟩

@[to_additive]

Depends on / 依赖: Commute, Commute.finset_image, finset_image, smul_comm
-/
instance smulCommClass_finset [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Finset γ) :=
⟨fun _ _ => Commute.finset_image smul_comm _ _⟩

@[to_additive]
/--
Instance `smulCommClass_finset'` / 实例 `smulCommClass_finset'`

English:
instance smulCommClass_finset'
  signature: [SMul α γ] [SMul β γ] [SMulCommClass α β γ]
  body: ⟨fun a s t => coe_injective by simp only [coe_smul_finset, coe_smul, smul_comm]⟩

@[to_additive]

中文:
实例 smulCommClass_finset'
  签名: [标量乘法 α γ] [标量乘法 β γ] [标量交换类 α β γ]
  定义体: ⟨fun a s t => coe_injective by simp only [coe_smul_finset, coe_smul, smul_comm]⟩

@[to_additive]

Depends on / 依赖: coe_injective, coe_smul, coe_smul_finset, smul_comm
-/
instance smulCommClass_finset' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Finset β) (Finset γ) :=
⟨fun a s t => coe_injective by simp only [coe_smul_finset, coe_smul, smul_comm]⟩

@[to_additive]
/--
Instance `smulCommClass_finset''` / 实例 `smulCommClass_finset''`

English:
instance smulCommClass_finset''
  signature: [SMul α γ] [SMul β γ] [SMulCommClass α β γ]
  body: haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _

@[to_additive]

中文:
实例 smulCommClass_finset''
  签名: [标量乘法 α γ] [标量乘法 β γ] [标量交换类 α β γ]
  定义体: haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _

@[to_additive]

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance smulCommClass_finset'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Finset α) β (Finset γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _

@[to_additive]
/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: [SMul α γ] [SMul β γ] [SMulCommClass α β γ]
  body: ⟨fun s t u => coe_injective by simp_rw [coe_smul, smul_comm]⟩

@[to_additive]

中文:
实例 smulCommClass
  签名: [标量乘法 α γ] [标量乘法 β γ] [标量交换类 α β γ]
  定义体: ⟨fun s t u => coe_injective by simp_rw [coe_smul, smul_comm]⟩

@[to_additive]

Depends on / 依赖: coe_injective, coe_smul, simp_rw, smul_comm
-/
instance smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Finset α) (Finset β) (Finset γ) :=
⟨fun s t u => coe_injective by simp_rw [coe_smul, smul_comm]⟩

@[to_additive]
/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ]
  body: ⟨fun a b s => by simp only [← image_smul, image_image, smul_assoc, Function.comp_def]⟩

中文:
实例 isScalarTower
  签名: [标量乘法 α β] [标量乘法 α γ] [标量乘法 β γ] [标量塔 α β γ]
  定义体: ⟨fun a b s => by simp only [← image_smul, image_image, smul_assoc, Function.comp_def]⟩

Depends on / 依赖: Function, Function.comp_def, comp_def, image_image, image_smul, smul_assoc
-/
instance isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Finset γ) :=
  ⟨fun a b s => by simp only [← image_smul, image_image, smul_assoc, Function.comp_def]⟩

variable [DecidableEq β]

@[to_additive]
/--
Instance `isScalarTower'` / 实例 `isScalarTower'`

English:
instance isScalarTower'
  signature: [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ]
  body: ⟨fun a s t => coe_injective by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩

@[to_additive]

中文:
实例 isScalarTower'
  签名: [标量乘法 α β] [标量乘法 α γ] [标量乘法 β γ] [标量塔 α β γ]
  定义体: ⟨fun a s t => coe_injective by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩

@[to_additive]

Depends on / 依赖: coe_injective, coe_smul, coe_smul_finset, smul_assoc
-/
instance isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Finset β) (Finset γ) :=
⟨fun a s t => coe_injective by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩

@[to_additive]
/--
Instance `isScalarTower''` / 实例 `isScalarTower''`

English:
instance isScalarTower''
  signature: [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ]
  body: ⟨fun a s t => coe_injective by simp only [coe_smul, smul_assoc]⟩

@[to_additive]

中文:
实例 isScalarTower''
  签名: [标量乘法 α β] [标量乘法 α γ] [标量乘法 β γ] [标量塔 α β γ]
  定义体: ⟨fun a s t => coe_injective by simp only [coe_smul, smul_assoc]⟩

@[to_additive]

Depends on / 依赖: coe_injective, coe_smul, smul_assoc
-/
instance isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Finset α) (Finset β) (Finset γ) :=
⟨fun a s t => coe_injective by simp only [coe_smul, smul_assoc]⟩

@[to_additive]
/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β]
  body: ⟨fun a s => coe_injective by simp only [coe_smul_finset, op_smul_eq_smul]⟩

中文:
实例 isCentralScalar
  签名: [标量乘法 α β] [标量乘法 αᵐᵒᵖ β] [中心标量 α β]
  定义体: ⟨fun a s => coe_injective by simp only [coe_smul_finset, op_smul_eq_smul]⟩

Depends on / 依赖: coe_injective, coe_smul_finset, op_smul_eq_smul
-/
instance isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Finset β) :=
⟨fun a s => coe_injective by simp only [coe_smul_finset, op_smul_eq_smul]⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of
`Finset α` on `Finset β`. -/
@[to_additive (attr := instance_reducible)
      /-- An additive action of an additive monoid `α` on a type `β` gives an additive action
      of `Finset α` on `Finset β` -/]
/--
Definition of `mulAction` / `mulAction` 的定义

English:
definition mulAction
  signature: [DecidableEq α] [Monoid α] [MulAction α β]
  body: image₂_assoc mul_smul
one_smul s := image₂_singleton_left.trans by simp_rw [one_smul, image_id']

中文:
定义 mulAction
  签名: [DecidableEq α] [幺半群 α] [乘法作用 α β]
  定义体: image₂_assoc mul_smul
one_smul s := image₂_singleton_left.trans by simp_rw [one_smul, image_id']
-/
protected def mulAction [DecidableEq α] [Monoid α] [MulAction α β] :
    MulAction (Finset α) (Finset β) where
  mul_smul _ _ _ := image₂_assoc mul_smul
one_smul s := image₂_singleton_left.trans by simp_rw [one_smul, image_id']

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `Finset β`.
-/
@[to_additive (attr := instance_reducible)
      /-- An additive action of an additive monoid on a type `β` gives an additive action
      on `Finset β`. -/]
/--
Definition of `mulActionFinset` / `mulActionFinset` 的定义

English:
definition mulActionFinset
  signature: [Monoid α] [MulAction α β]
  body: coe_injective.mulAction _ coe_smul_finset

scoped[Pointwise]
  attribute [instance]
    Finset.mulActionFinset Finset.addActionFinset Finset.mulAction Finset.addAction

中文:
定义 mulActionFinset
  签名: [幺半群 α] [乘法作用 α β]
  定义体: coe_injective.mulAction _ coe_smul_finset

scoped[Pointwise]
  attribute [instance]
    Finset.mulActionFinset Finset.addActionFinset Finset.mulAction Finset.addAction
-/
protected def mulActionFinset [Monoid α] [MulAction α β] : MulAction α (Finset β) :=
  coe_injective.mulAction _ coe_smul_finset

scoped[Pointwise]
  attribute [instance]
    Finset.mulActionFinset Finset.addActionFinset Finset.mulAction Finset.addAction

end Instances

section Mul

variable [Mul α] [DecidableEq α] {s t u : Finset α} {a : α}

open scoped RightActions in
/--
lemma `mul_singleton` / 引理 `mul_singleton`

English:
lemma mul_singleton
  given: (a : α)
  statement: s * {a} = s <• a
  proof: image₂_singleton_right

中文:
引理 mul_singleton
  条件: (a : α)
  结论: s * {a} = s <• a
  证明: image₂_singleton_right
-/
@[to_additive] lemma mul_singleton (a : α) : s * {a} = s <• a := image₂_singleton_right
/--
lemma `singleton_mul` / 引理 `singleton_mul`

English:
lemma singleton_mul
  given: (a : α)
  statement: {a} * s = a • s
  proof: image₂_singleton_left

中文:
引理 singleton_mul
  条件: (a : α)
  结论: {a} * s = a • s
  证明: image₂_singleton_left
-/
@[to_additive] lemma singleton_mul (a : α) : {a} * s = a • s := image₂_singleton_left

/--
lemma `smul_finset_subset_mul` / 引理 `smul_finset_subset_mul`

English:
lemma smul_finset_subset_mul
  statement: a in s -> a • t subseteq s * t
  proof: image_subset_image₂_right

@[to_additive]

中文:
引理 smul_finset_subset_mul
  结论: a in s -> a • t subseteq s * t
  证明: image_subset_image₂_right

@[to_additive]
-/
@[to_additive] lemma smul_finset_subset_mul : a in s -> a • t subseteq s * t := image_subset_image₂_right

@[to_additive]
/--
theorem `op_smul_finset_subset_mul` / 定理 `op_smul_finset_subset_mul`

English:
theorem op_smul_finset_subset_mul
  statement: a in t -> op a • s subseteq s * t
  proof: image_subset_image₂_left

@[to_additive (attr := simp)]

中文:
定理 op_smul_finset_subset_mul
  结论: a in t -> op a • s subseteq s * t
  证明: image_subset_image₂_left

@[to_additive (attr := simp)]
-/
theorem op_smul_finset_subset_mul : a in t -> op a • s subseteq s * t :=
  image_subset_image₂_left

@[to_additive (attr := simp)]
/--
theorem `biUnion_op_smul_finset` / 定理 `biUnion_op_smul_finset`

English:
theorem biUnion_op_smul_finset
  given: (s t : Finset α)
  statement: (t.biUnion fun a => op a • s) = s * t
  proof: biUnion_image_right

@[to_additive]

中文:
定理 biUnion_op_smul_finset
  条件: (s t : 有限集 α)
  结论: (t.biUnion fun a => op a • s) = s * t
  证明: biUnion_image_right

@[to_additive]

Depends on / 依赖: biUnion_image_right
-/
theorem biUnion_op_smul_finset (s t : Finset α) : (t.biUnion fun a => op a • s) = s * t :=
  biUnion_image_right

@[to_additive]
/--
theorem `mul_subset_iff_left` / 定理 `mul_subset_iff_left`

English:
theorem mul_subset_iff_left
  statement: s * t subseteq u ↔ forall a in s, a • t subseteq u
  proof: image₂_subset_iff_left

@[to_additive]

中文:
定理 mul_subset_iff_left
  结论: s * t subseteq u ↔ 对任意 a in s, a • t subseteq u
  证明: image₂_subset_iff_left

@[to_additive]
-/
theorem mul_subset_iff_left : s * t subseteq u ↔ forall a in s, a • t subseteq u :=
  image₂_subset_iff_left

@[to_additive]
/--
theorem `mul_subset_iff_right` / 定理 `mul_subset_iff_right`

English:
theorem mul_subset_iff_right
  statement: s * t subseteq u ↔ forall b in t, op b • s subseteq u
  proof: image₂_subset_iff_right

中文:
定理 mul_subset_iff_right
  结论: s * t subseteq u ↔ 对任意 b in t, op b • s subseteq u
  证明: image₂_subset_iff_right
-/
theorem mul_subset_iff_right : s * t subseteq u ↔ forall b in t, op b • s subseteq u :=
  image₂_subset_iff_right

end Mul

section Semigroup

variable [Semigroup α] [DecidableEq α]

@[to_additive]
/--
theorem `op_smul_finset_mul_eq_mul_smul_finset` / 定理 `op_smul_finset_mul_eq_mul_smul_finset`

English:
theorem op_smul_finset_mul_eq_mul_smul_finset
  given: (a : α) (s : Finset α) (t : Finset α)
  proof: op_smul_finset_smul_eq_smul_smul_finset _ _ _ fun _ _ _ => mul_assoc _ _ _

中文:
定理 op_smul_finset_mul_eq_mul_smul_finset
  条件: (a : α) (s : 有限集 α) (t : 有限集 α)
  证明: op_smul_finset_smul_eq_smul_smul_finset _ _ _ fun _ _ _ => mul_assoc _ _ _

Depends on / 依赖: mul_assoc, op_smul_finset_smul_eq_smul_smul_finset
-/
theorem op_smul_finset_mul_eq_mul_smul_finset (a : α) (s : Finset α) (t : Finset α) :
    op a • s * t = s * a • t :=
  op_smul_finset_smul_eq_smul_smul_finset _ _ _ fun _ _ _ => mul_assoc _ _ _

end Semigroup

section IsLeftCancelSMul
variable [SMul α β] [IsLeftCancelSMul α β] [DecidableEq β]

@[to_additive]
/--
theorem `pairwiseDisjoint_smul_iff` / 定理 `pairwiseDisjoint_smul_iff`

English:
theorem pairwiseDisjoint_smul_iff
  given: {s : Set α} {t : Finset β}
  proof: by
  simp_rw [← pairwiseDisjoint_coe, coe_smul_finset, Set.pairwiseDisjoint_smul_iff]

中文:
定理 pairwiseDisjoint_smul_iff
  条件: {s : 集合 α} {t : 有限集 β}
  证明: by
  simp_rw [← pairwiseDisjoint_coe, coe_smul_finset, Set.pairwiseDisjoint_smul_iff]

Depends on / 依赖: Set.pairwiseDisjoint_smul_iff, coe_smul_finset, pairwiseDisjoint_coe, pairwiseDisjoint_smul_iff, simp_rw
-/
theorem pairwiseDisjoint_smul_iff {s : Set α} {t : Finset β} :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t : Set (α × β)).InjOn fun p => p.1 • p.2 := by
  simp_rw [← pairwiseDisjoint_coe, coe_smul_finset, Set.pairwiseDisjoint_smul_iff]

end IsLeftCancelSMul

@[to_additive]
/--
theorem `image_smul_distrib` / 定理 `image_smul_distrib`

English:
theorem image_smul_distrib
  statement: [DecidableEq α] [DecidableEq β] [Mul α] [Mul β] [FunLike F α β]
  proof: image_comm map_mul _ _

中文:
定理 image_smul_distrib
  结论: [DecidableEq α] [DecidableEq β] [乘法 α] [乘法 β] [函数状 F α β]
  证明: image_comm map_mul _ _

Depends on / 依赖: image_comm, map_mul
-/
theorem image_smul_distrib [DecidableEq α] [DecidableEq β] [Mul α] [Mul β] [FunLike F α β]
    [MulHomClass F α β] (f : F) (a : α) (s : Finset α) : (a • s).image f = f a • s.image f :=
image_comm map_mul _ _

section Group

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

@[to_additive (attr := simp)]
/--
theorem `smul_mem_smul_finset_iff` / 定理 `smul_mem_smul_finset_iff`

English:
theorem smul_mem_smul_finset_iff
  given: (a : α)
  statement: a • b in a • s ↔ b in s
  proof: (MulAction.injective _).mem_finset_image

@[to_additive (attr := simp)]

中文:
定理 smul_mem_smul_finset_iff
  条件: (a : α)
  结论: a • b in a • s ↔ b in s
  证明: (MulAction.injective _).mem_finset_image

@[to_additive (attr := simp)]

Depends on / 依赖: MulAction, MulAction.injective, injective, mem_finset_image
-/
theorem smul_mem_smul_finset_iff (a : α) : a • b in a • s ↔ b in s :=
  (MulAction.injective _).mem_finset_image

@[to_additive (attr := simp)]
/--
lemma `mul_mem_smul_finset_iff` / 引理 `mul_mem_smul_finset_iff`

English:
lemma mul_mem_smul_finset_iff
  given: [DecidableEq α] (a : α) {b : α} {s : Finset α}
  proof: smul_mem_smul_finset_iff _

@[to_additive]

中文:
引理 mul_mem_smul_finset_iff
  条件: [DecidableEq α] (a : α) {b : α} {s : 有限集 α}
  证明: smul_mem_smul_finset_iff _

@[to_additive]

Depends on / 依赖: smul_mem_smul_finset_iff
-/
lemma mul_mem_smul_finset_iff [DecidableEq α] (a : α) {b : α} {s : Finset α} :
    a * b in a • s ↔ b in s := smul_mem_smul_finset_iff _

@[to_additive]
/--
theorem `inv_smul_mem_iff` / 定理 `inv_smul_mem_iff`

English:
theorem inv_smul_mem_iff
  statement: a⁻¹ • b in s ↔ b in a • s
  proof: by
  rw [← smul_mem_smul_finset_iff a]; rw [smul_inv_smul]

@[to_additive]

中文:
定理 inv_smul_mem_iff
  结论: a⁻¹ • b in s ↔ b in a • s
  证明: by
  rw [← smul_mem_smul_finset_iff a]; rw [smul_inv_smul]

@[to_additive]

Depends on / 依赖: smul_inv_smul, smul_mem_smul_finset_iff
-/
theorem inv_smul_mem_iff : a⁻¹ • b in s ↔ b in a • s := by
  rw [← smul_mem_smul_finset_iff a]; rw [smul_inv_smul]

@[to_additive]
/--
theorem `mem_inv_smul_finset_iff` / 定理 `mem_inv_smul_finset_iff`

English:
theorem mem_inv_smul_finset_iff
  statement: b in a⁻¹ • s ↔ a • b in s
  proof: by
  rw [← smul_mem_smul_finset_iff a]; rw [smul_inv_smul]

@[to_additive (attr := simp)]

中文:
定理 mem_inv_smul_finset_iff
  结论: b in a⁻¹ • s ↔ a • b in s
  证明: by
  rw [← smul_mem_smul_finset_iff a]; rw [smul_inv_smul]

@[to_additive (attr := simp)]

Depends on / 依赖: smul_inv_smul, smul_mem_smul_finset_iff
-/
theorem mem_inv_smul_finset_iff : b in a⁻¹ • s ↔ a • b in s := by
  rw [← smul_mem_smul_finset_iff a]; rw [smul_inv_smul]

@[to_additive (attr := simp)]
/--
theorem `smul_finset_subset_smul_finset_iff` / 定理 `smul_finset_subset_smul_finset_iff`

English:
theorem smul_finset_subset_smul_finset_iff
  statement: a • s subseteq a • t ↔ s subseteq t
  proof: image_subset_image_iff MulAction.injective _

@[to_additive]

中文:
定理 smul_finset_subset_smul_finset_iff
  结论: a • s subseteq a • t ↔ s subseteq t
  证明: image_subset_image_iff MulAction.injective _

@[to_additive]

Depends on / 依赖: MulAction, MulAction.injective, image_subset_image_iff, injective
-/
theorem smul_finset_subset_smul_finset_iff : a • s subseteq a • t ↔ s subseteq t :=
image_subset_image_iff MulAction.injective _

@[to_additive]
/--
theorem `smul_finset_subset_iff` / 定理 `smul_finset_subset_iff`

English:
theorem smul_finset_subset_iff
  statement: a • s subseteq t ↔ s subseteq a⁻¹ • t
  proof: by
  simp_rw [← coe_subset]
  push_cast
  exact Set.smul_set_subset_iff_subset_inv_smul_set

@[to_additive]

中文:
定理 smul_finset_subset_iff
  结论: a • s subseteq t ↔ s subseteq a⁻¹ • t
  证明: by
  simp_rw [← coe_subset]
  push_cast
  exact Set.smul_set_subset_iff_subset_inv_smul_set

@[to_additive]

Depends on / 依赖: Set.smul_set_subset_iff_subset_inv_smul_set, coe_subset, simp_rw, smul_set_subset_iff_subset_inv_smul_set
-/
theorem smul_finset_subset_iff : a • s subseteq t ↔ s subseteq a⁻¹ • t := by
  simp_rw [← coe_subset]
  push_cast
  exact Set.smul_set_subset_iff_subset_inv_smul_set

@[to_additive]
/--
theorem `subset_smul_finset_iff` / 定理 `subset_smul_finset_iff`

English:
theorem subset_smul_finset_iff
  statement: s subseteq a • t ↔ a⁻¹ • s subseteq t
  proof: by
  simp_rw [← coe_subset]
  push_cast
  exact Set.subset_smul_set_iff

@[to_additive]

中文:
定理 subset_smul_finset_iff
  结论: s subseteq a • t ↔ a⁻¹ • s subseteq t
  证明: by
  simp_rw [← coe_subset]
  push_cast
  exact Set.subset_smul_set_iff

@[to_additive]

Depends on / 依赖: DivisionMonoid, Group.toDivisionMonoid, Set.subset_smul_set_iff, coe_subset, simp_rw, subset_smul_set_iff, toDivisionMonoid
-/
theorem subset_smul_finset_iff : s subseteq a • t ↔ a⁻¹ • s subseteq t := by
  simp_rw [← coe_subset]
  push_cast
  exact Set.subset_smul_set_iff

@[to_additive]
/--
theorem `smul_finset_inter` / 定理 `smul_finset_inter`

English:
theorem smul_finset_inter
  statement: a • (s inter t) = a • s inter a • t
  proof: image_inter _ _ MulAction.injective a

@[to_additive]

中文:
定理 smul_finset_inter
  结论: a • (s inter t) = a • s inter a • t
  证明: image_inter _ _ MulAction.injective a

@[to_additive]

Depends on / 依赖: CancelMonoid, Group.toCancelMonoid, MulAction, MulAction.injective, image_inter, injective, toCancelMonoid
-/
theorem smul_finset_inter : a • (s inter t) = a • s inter a • t :=
image_inter _ _ MulAction.injective a

@[to_additive]
/--
theorem `smul_finset_sdiff` / 定理 `smul_finset_sdiff`

English:
theorem smul_finset_sdiff
  statement: a • (s \ t) = a • s \ a • t
  proof: image_sdiff _ _ MulAction.injective a

中文:
定理 smul_finset_sdiff
  结论: a • (s \ t) = a • s \ a • t
  证明: image_sdiff _ _ MulAction.injective a

Depends on / 依赖: CancelCommMonoid, CommGroup, CommGroup.toCancelCommMonoid, MulAction, MulAction.injective, image_sdiff, injective, toCancelCommMonoid
-/
theorem smul_finset_sdiff : a • (s \ t) = a • s \ a • t :=
image_sdiff _ _ MulAction.injective a

open scoped symmDiff in
@[to_additive]
/--
theorem `smul_finset_symmDiff` / 定理 `smul_finset_symmDiff`

English:
theorem smul_finset_symmDiff
  statement: a • s ∆ t = (a • s) ∆ (a • t)
  proof: image_symmDiff _ _ MulAction.injective a

@[to_additive (attr := simp)]

中文:
定理 smul_finset_symmDiff
  结论: a • s ∆ t = (a • s) ∆ (a • t)
  证明: image_symmDiff _ _ MulAction.injective a

@[to_additive (attr := simp)]

Depends on / 依赖: CommGroup, CommGroup.toDivisionCommMonoid, DivisionCommMonoid, MulAction, MulAction.injective, image_symmDiff, injective, toDivisionCommMonoid
-/
theorem smul_finset_symmDiff : a • s ∆ t = (a • s) ∆ (a • t) :=
image_symmDiff _ _ MulAction.injective a

@[to_additive (attr := simp)]
/--
theorem `smul_finset_univ` / 定理 `smul_finset_univ`

English:
theorem smul_finset_univ
  given: [Fintype β]
  statement: a • (univ : Finset β) = univ
  proof: image_univ_of_surjective MulAction.surjective a

@[to_additive (attr := simp)]

中文:
定理 smul_finset_univ
  条件: [有限类型 β]
  结论: a • (univ : 有限集 β) = univ
  证明: image_univ_of_surjective MulAction.surjective a

@[to_additive (attr := simp)]

Depends on / 依赖: MulAction, MulAction.surjective, image_univ_of_surjective, surjective
-/
theorem smul_finset_univ [Fintype β] : a • (univ : Finset β) = univ :=
image_univ_of_surjective MulAction.surjective a

@[to_additive (attr := simp)]
/--
theorem `smul_finset_eq_univ` / 定理 `smul_finset_eq_univ`

English:
theorem smul_finset_eq_univ
  given: [Fintype β]
  statement: a • s = univ ↔ s = univ
  proof: by
  rw [smul_eq_iff_eq_inv_smul]; rw [smul_finset_univ]

@[to_additive (attr := simp)]

中文:
定理 smul_finset_eq_univ
  条件: [有限类型 β]
  结论: a • s = univ ↔ s = univ
  证明: by
  rw [smul_eq_iff_eq_inv_smul]; rw [smul_finset_univ]

@[to_additive (attr := simp)]

Depends on / 依赖: smul_eq_iff_eq_inv_smul, smul_finset_univ
-/
theorem smul_finset_eq_univ [Fintype β] : a • s = univ ↔ s = univ := by
  rw [smul_eq_iff_eq_inv_smul]; rw [smul_finset_univ]

@[to_additive (attr := simp)]
/--
theorem `smul_univ` / 定理 `smul_univ`

English:
theorem smul_univ
  given: [Fintype β] {s : Finset α} (hs : s.Nonempty)
  statement: s • (univ : Finset β) = univ
  proof: coe_injective by
    push_cast
    exact Set.smul_univ hs

@[to_additive (attr := simp)]

中文:
定理 smul_univ
  条件: [有限类型 β] {s : 有限集 α} (hs : s.非空)
  结论: s • (univ : 有限集 β) = univ
  证明: coe_injective by
    push_cast
    exact Set.smul_univ hs

@[to_additive (attr := simp)]

Depends on / 依赖: Set.smul_univ, coe_injective, smul_univ
-/
theorem smul_univ [Fintype β] {s : Finset α} (hs : s.Nonempty) : s • (univ : Finset β) = univ :=
coe_injective by
    push_cast
    exact Set.smul_univ hs

@[to_additive (attr := simp)]
/--
theorem `card_smul_finset` / 定理 `card_smul_finset`

English:
theorem card_smul_finset
  given: (a : α) (s : Finset β)
  statement: (a • s).card = s.card
  proof: card_image_of_injective _ MulAction.injective _

中文:
定理 card_smul_finset
  条件: (a : α) (s : 有限集 β)
  结论: (a • s).card = s.card
  证明: card_image_of_injective _ MulAction.injective _

Depends on / 依赖: MulAction, MulAction.injective, card_image_of_injective, injective
-/
theorem card_smul_finset (a : α) (s : Finset β) : (a • s).card = s.card :=
card_image_of_injective _ MulAction.injective _

/-- If the left cosets of `t` by elements of `s` are disjoint (but not necessarily distinct!), then
the size of `t` divides the size of `s • t`. -/
@[to_additive /-- If the left cosets of `t` by elements of `s` are disjoint (but not necessarily
distinct!), then the size of `t` divides the size of `s +ᵥ t`. -/]
/--
theorem `card_dvd_card_smul_right` / 定理 `card_dvd_card_smul_right`

English:
theorem card_dvd_card_smul_right
  given: {s : Finset α}
  proof: card_dvd_card_image₂_right fun _ _ => MulAction.injective _

中文:
定理 card_dvd_card_smul_right
  条件: {s : 有限集 α}
  证明: card_dvd_card_image₂_right fun _ _ => MulAction.injective _

Depends on / 依赖: MulAction, MulAction.injective, injective
-/
theorem card_dvd_card_smul_right {s : Finset α} :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id -> t.card ∣ (s • t).card :=
  card_dvd_card_image₂_right fun _ _ => MulAction.injective _

variable [DecidableEq α]

/-- If the right cosets of `s` by elements of `t` are disjoint (but not necessarily distinct!), then
the size of `s` divides the size of `s * t`. -/
@[to_additive /-- If the right cosets of `s` by elements of `t` are disjoint (but not necessarily
distinct!), then the size of `s` divides the size of `s + t`. -/]
/--
theorem `card_dvd_card_mul_left` / 定理 `card_dvd_card_mul_left`

English:
theorem card_dvd_card_mul_left
  given: {s t : Finset α}
  proof: card_dvd_card_image₂_left fun _ _ => mul_left_injective _

中文:
定理 card_dvd_card_mul_left
  条件: {s t : 有限集 α}
  证明: card_dvd_card_image₂_left fun _ _ => mul_left_injective _

Depends on / 依赖: mul_left_injective
-/
theorem card_dvd_card_mul_left {s t : Finset α} :
    ((fun b => s.image fun a => a * b) '' (t : Set α)).PairwiseDisjoint id ->
      s.card ∣ (s * t).card :=
  card_dvd_card_image₂_left fun _ _ => mul_left_injective _

/-- If the left cosets of `t` by elements of `s` are disjoint (but not necessarily distinct!), then
the size of `t` divides the size of `s * t`. -/
@[to_additive /-- If the left cosets of `t` by elements of `s` are disjoint (but not necessarily
distinct!), then the size of `t` divides the size of `s + t`. -/]
/--
theorem `card_dvd_card_mul_right` / 定理 `card_dvd_card_mul_right`

English:
theorem card_dvd_card_mul_right
  given: {s t : Finset α}
  proof: card_dvd_card_image₂_right fun _ _ => mul_right_injective _

@[to_additive (attr := simp)]

中文:
定理 card_dvd_card_mul_right
  条件: {s t : 有限集 α}
  证明: card_dvd_card_image₂_right fun _ _ => mul_right_injective _

@[to_additive (attr := simp)]

Depends on / 依赖: mul_right_injective
-/
theorem card_dvd_card_mul_right {s t : Finset α} :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id -> t.card ∣ (s * t).card :=
  card_dvd_card_image₂_right fun _ _ => mul_right_injective _

@[to_additive (attr := simp)]
/--
lemma `inv_smul_finset_distrib` / 引理 `inv_smul_finset_distrib`

English:
lemma inv_smul_finset_distrib
  given: (a : α) (s : Finset α)
  statement: (a • s)⁻¹ = op a⁻¹ • s⁻¹
  proof: by
  ext; simp [← inv_smul_mem_iff]

@[to_additive (attr := simp)]

中文:
引理 inv_smul_finset_distrib
  条件: (a : α) (s : 有限集 α)
  结论: (a • s)⁻¹ = op a⁻¹ • s⁻¹
  证明: by
  ext; simp [← inv_smul_mem_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_smul_mem_iff
-/
lemma inv_smul_finset_distrib (a : α) (s : Finset α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹ := by
  ext; simp [← inv_smul_mem_iff]

@[to_additive (attr := simp)]
/--
lemma `inv_op_smul_finset_distrib` / 引理 `inv_op_smul_finset_distrib`

English:
lemma inv_op_smul_finset_distrib
  given: (a : α) (s : Finset α)
  statement: (op a • s)⁻¹ = a⁻¹ • s⁻¹
  proof: by
  ext; simp [← inv_smul_mem_iff]

中文:
引理 inv_op_smul_finset_distrib
  条件: (a : α) (s : 有限集 α)
  结论: (op a • s)⁻¹ = a⁻¹ • s⁻¹
  证明: by
  ext; simp [← inv_smul_mem_iff]

Depends on / 依赖: inv_smul_mem_iff
-/
lemma inv_op_smul_finset_distrib (a : α) (s : Finset α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹ := by
  ext; simp [← inv_smul_mem_iff]

end Group
end Finset

namespace Fintype
variable {ι : Type*} {α β : ι -> Type*} [Fintype ι] [DecidableEq ι] [forall i, DecidableEq (β i)]

@[to_additive]
/--
lemma `piFinset_smul` / 引理 `piFinset_smul`

English:
lemma piFinset_smul
  given: [forall i, SMul (α i) (β i)] (s : forall i, Finset (α i)) (t : forall i, Finset (β i))
  proof: piFinset_image₂ _ _ _

@[to_additive]

中文:
引理 piFinset_smul
  条件: [对任意 i, 标量乘法 (α i) (β i)] (s : 对任意 i, 有限集 (α i)) (t : 对任意 i, 有限集 (β i))
  证明: piFinset_image₂ _ _ _

@[to_additive]
-/
lemma piFinset_smul [forall i, SMul (α i) (β i)] (s : forall i, Finset (α i)) (t : forall i, Finset (β i)) :
    piFinset (fun i => s i • t i) = piFinset s • piFinset t := piFinset_image₂ _ _ _

@[to_additive]
/--
lemma `piFinset_smul_finset` / 引理 `piFinset_smul_finset`

English:
lemma piFinset_smul_finset
  given: [forall i, SMul (α i) (β i)] (a : forall i, α i) (s : forall i, Finset (β i))
  proof: piFinset_image _ _

中文:
引理 piFinset_smul_finset
  条件: [对任意 i, 标量乘法 (α i) (β i)] (a : 对任意 i, α i) (s : 对任意 i, 有限集 (β i))
  证明: piFinset_image _ _

Depends on / 依赖: piFinset_image
-/
lemma piFinset_smul_finset [forall i, SMul (α i) (β i)] (a : forall i, α i) (s : forall i, Finset (β i)) :
    piFinset (fun i => a i • s i) = a • piFinset s := piFinset_image _ _

-- Note: We don't currently state `piFinset_vsub` because there's no
-- `[∀ i, VSub (β i) (α i)] → VSub (∀ i, β i) (∀ i, α i)` instance

end Fintype

/--
Instance `Nat.decidablePred_mem_vadd_set` / 实例 `Nat.decidablePred_mem_vadd_set`

English:
instance Nat.decidablePred_mem_vadd_set
  signature: {s : Set Nat} [DecidablePred (· in s)] (a : Nat)
  body: fun n => decidable_of_iff' (a <= n ∧ n - a in s) by
    simp only [Set.mem_vadd_set, vadd_eq_add]; aesop

中文:
实例 自然数.decidablePred_mem_vadd_set
  签名: {s : 集合 自然数} [DecidablePred (· in s)] (a : 自然数)
  定义体: fun n => decidable_of_iff' (a <= n ∧ n - a in s) by
    simp only [Set.mem_vadd_set, vadd_eq_add]; aesop

Depends on / 依赖: Set.mem_vadd_set, decidable_of_iff, mem_vadd_set, vadd_eq_add
-/
instance Nat.decidablePred_mem_vadd_set {s : Set Nat} [DecidablePred (· in s)] (a : Nat) :
    DecidablePred (· in a +ᵥ s) :=
fun n => decidable_of_iff' (a <= n ∧ n - a in s) by
    simp only [Set.mem_vadd_set, vadd_eq_add]; aesop
